/*
    Copyright (C) 2018, Jianwen Li (lijwen2748@gmail.com), Iowa State University

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*/

/*
	Author: Jianwen Li
	Update Date: October 17, 2017
	Data Structure for models
*/

#include "model.h"
#include "utility.h"
#include <stdlib.h>
#include <iostream>
#include <assert.h>
#include <vector>

using namespace std;

namespace car{

	Model::Model (aiger* aig, int unroll_max,const bool verbose)
	{
	    verbose_ = verbose;
		unroll_max_ = unroll_max;
	//According to aiger format, inputs should be [1 ... num_inputs_]
	//and latches should be [num_inputs+1 ... num_latches+num_inputs]]
		num_inputs_ = aig->num_inputs;
		num_latches_ = aig->num_latches;
		num_ands_ = aig->num_ands;
		num_constraints_ = aig->num_constraints;
		num_outputs_ = aig->num_outputs;
		true_ = aig->maxvar+1;
		false_ = -true_;
		//preserve two more ids for TRUE (max_id_ - 1) and FALSE (max_id_)
		max_id_ = aig->maxvar+2;
		

		collect_trues (aig);
		
		set_constraints (aig);
		set_outputs (aig);
		
		set_init (aig);
		
		create_next_map (aig);
		create_clauses (aig);
	}
	
	void Model::collect_trues (const aiger* aig)
	{
		for (int i = 0; i < aig->num_ands; i ++)
		{
			aiger_and& aa = aig->ands[i];
			//and gate is always an even number in aiger
			assert (aa.lhs % 2 == 0);
			if (is_true (aa.rhs0) && is_true (aa.rhs1))
				trues_.insert (aa.lhs);
			else if (is_false (aa.rhs0) || is_false (aa.rhs1))
				trues_.insert (aa.lhs + 1);
		}
	}
	
	void Model::create_next_map (const aiger* aig)
	{
		for (int i = 0; i < aig->num_latches; i ++)
		{
			int val = (int)aig->latches[i].lit;
			//a latch should not be a negative number
			assert (val % 2 == 0);
			val = val / 2;
			//make sure our assumption about latches is correct
			assert (val == (num_inputs_ + 1 + i));
			
			//pay attention to the special case when next_val = 0 or 1
			if (is_false (aig->latches[i].next))  //FALSE
			{
				next_map_.insert (std::pair<int, int> (val, false_));
				insert_to_reverse_next_map (false_, val);
			}
			else if (is_true (aig->latches[i].next)) //TRUE
			{
				next_map_.insert (std::pair<int, int> (val, true_));
				insert_to_reverse_next_map (true_, val);
			}
			else
			{
				int next_val = (int) aig->latches[i].next;
				next_val = (next_val % 2 == 0) ? (next_val/2) : -(next_val/2);
				next_map_.insert (std::pair<int, int> (val, next_val));
				insert_to_reverse_next_map (abs (next_val), (next_val > 0) ? val : -val);
			}
			
		}
	}
	
	void Model::insert_to_reverse_next_map (const int index, const int val)
	{
	    reverseNextMap::iterator it = reverse_next_map_.find (index);
	    if (it == reverse_next_map_.end ())
	    {
	        vector<int> v;
	        v.push_back (val);
	        reverse_next_map_.insert (std::pair<int, vector<int> > (index, v));
	    }
	    else
	        (it->second).push_back (val);
	}
	
	void Model::create_clauses (const aiger* aig)
	{
	    //contraints, outputs and latches gates are stored in order, 
	    //as the need for start solver construction
	    hash_set<unsigned> exist_gates;
		hash_set<unsigned> coi_exist_gates;
		vector<unsigned> gates;
		gates.resize (max_id_+1, 0);
		//create clauses for constraints
		collect_necessary_gates (aig, aig->constraints, aig->num_constraints, exist_gates, gates);
		
		for (vector<unsigned>::iterator it = gates.begin (); it != gates.end (); it ++)
		{
		    if (*it == 0) continue; 
			aiger_and* aa = aiger_is_and (const_cast<aiger*>(aig), *it);
			assert (aa != NULL);
			add_clauses_from_gate (aa);
		}
		for(auto it = cls_.begin();it != cls_.end();++it) coi_cls_.emplace_back(*it); //copy cls_ to coi_cls_
		
		set_outputs_start ();
		
		//create clauses for outputs
		gates.resize (max_id_+1, 0);
		collect_necessary_gates (aig, aig->outputs, aig->num_outputs, exist_gates, gates);
		
		for (vector<unsigned>::iterator it = gates.begin (); it != gates.end (); it ++)
		{
		    if (*it == 0) continue;
			aiger_and* aa = aiger_is_and (const_cast<aiger*>(aig), *it);
			assert (aa != NULL);
			//add_clauses_from_gate (aa);
			add_prime_clauses_from_gate (aa);
			//bmc_add_prime_clauses_from_gate (aa);  //add bmc needed clause
		}

		//create coi clauses for output
		gates.resize (max_id_+1, 0);
		collect_necessary_gates_for_coi (aig, aig->outputs, aig->num_outputs, coi_exist_gates, gates);
		for (vector<unsigned>::iterator it = gates.begin (); it != gates.end (); it ++)
		{
		    if (*it == 0) continue;
			aiger_and* aa = aiger_is_and (const_cast<aiger*>(aig), *it);
			assert (aa != NULL);
			//add_clauses_from_gate (aa);
			add_prime_clauses_from_gate_for_coi (aa);
			//bmc_add_prime_clauses_from_gate (aa);  //add bmc needed clause
		}

		set_latches_start ();
		
		//create clauses for latches
		gates.resize (max_id_+1, 0);
		collect_necessary_gates (aig, aig->latches, aig->num_latches, exist_gates, gates, true);
		for (vector<unsigned>::iterator it = gates.begin (); it != gates.end (); it ++)
		{
		    if (*it == 0) continue;
			aiger_and* aa = aiger_is_and (const_cast<aiger*>(aig), *it);
			assert (aa != NULL);
			add_clauses_from_gate (aa);
		}
		
		//create clauses for next map
		for (auto it = next_map_.begin (); it != next_map_.end (); ++it){
			//add clauses for prime (it->first) <-> it->second
			cls_.push_back (clause (prime (-(it->first)), it->second));
			cls_.push_back (clause (prime (it->first), -(it->second)));
			coi_cls_.push_back (clause (prime (-(it->first)), it->second));
			coi_cls_.push_back (clause (prime (it->first), -(it->second)));
		}
		
		//create clauses for true
		cls_.push_back (clause (true_));
		cls_.push_back (clause (prime (true_)));

		coi_cls_.push_back (clause (true_));
		coi_cls_.push_back (clause (prime (true_)));
		
		for(int i=0;i<constraints_.size();i++)
			cls_.push_back(clause(constraints_[i]));

		for(int i=0;i<constraints_.size();i++)
			coi_cls_.push_back(clause(constraints_[i]));
	}
	
	
	void Model::collect_necessary_gates (const aiger* aig, const aiger_symbol* as, const int as_size, 
	                                        hash_set<unsigned>& exist_gates, vector<unsigned>& gates, bool next)
	{
		for (int i = 0; i < as_size; i ++)
		{
			aiger_and* aa;
			if (next) 
			    aa = necessary_gate (as[i].next, aig);
			else
			{
			    aa = necessary_gate (as[i].lit, aig);
			    if (aa == NULL)
			    {
			    	if (is_true (as[i].lit))
			    		outputs_[i] = true_;
			    	else if (is_false (as[i].lit))
			    		outputs_[i] = false_;
			    }
			}
			recursively_add (aa, aig, exist_gates, gates);	
		}
		
	}
	
	void Model::collect_necessary_gates_for_coi (const aiger* aig, const aiger_symbol* as, const int as_size, 
	                                        hash_set<unsigned>& exist_gates, vector<unsigned>& gates)
	{
		//exist_gates here stand for andgates and latches
		for (int i = 0; i < as_size; i ++)
		{
		//in case the output is true or false
		if (is_true (as[i].lit))
			outputs_[i] = true_;
		else if (is_false (as[i].lit))
			outputs_[i] = false_;
		
		recursively_add_for_coi (as[i].lit, aig, exist_gates, gates);	
		}
		
	}
	
	aiger_and* Model::necessary_gate (const unsigned id, const aiger* aig)
	{
		if (!is_true (id) && !is_false (id))
			return aiger_is_and (const_cast<aiger*> (aig), (id % 2 == 0) ? id : (id-1));
			
		return NULL;
	}

	aiger_symbol* Model::necessary_latch (const unsigned id, const aiger* aig)
	{
		if (!is_true (id) && !is_false (id))
			return aiger_is_latch (const_cast<aiger*> (aig), (id % 2 == 0) ? id : (id-1));
			
		return NULL;
	}
	
	void Model::recursively_add (const aiger_and* aa, const aiger* aig, hash_set<unsigned>& exist_gates, vector<unsigned>& gates)
	{
		if (aa == NULL)
			return;
		if (exist_gates.find (aa->lhs) != exist_gates.end ())
			return;
		
		gates[aa->lhs/2] = aa->lhs;
		exist_gates.insert (aa->lhs);
		aiger_and* aa0 = necessary_gate (aa->rhs0, aig);
		recursively_add (aa0, aig, exist_gates, gates);
		
		aiger_and* aa1 = necessary_gate (aa->rhs1, aig);
		recursively_add (aa1, aig, exist_gates, gates);
	}

	void Model::recursively_add_for_coi (const unsigned id, const aiger* aig, hash_set<unsigned>& exist_gates, vector<unsigned>& gates)
	{
		//gates here stand for andgates and latches, the same for exist_gates
		if (is_true (id) || is_false (id)) return;
		unsigned true_id = id/2;
		unsigned positive_id = (id % 2 == 0) ? id : (id-1);
		// if id is input -> return 
		if (true_id <= num_inputs_) return;

		if (exist_gates.find (positive_id) != exist_gates.end ())
			return;
		// if id is latch  -> recursivly add aa's next 
		if (true_id <= (num_inputs_ + num_latches_))
		{
			aiger_symbol *lat;
			lat = necessary_latch(id,aig);
			assert(lat != NULL);
			exist_gates.insert (positive_id);
			recursively_add_for_coi (lat->next, aig, exist_gates, gates);
		}
		else
		{
			// if id is andgate -> recursivly add id's rhs0 and rhs1
			aiger_and* aa;
			aa = necessary_gate (id, aig);
			assert(aa != NULL);
			gates[aa->lhs/2] = aa->lhs;
			exist_gates.insert (aa->lhs);
			unsigned aa0 = aa->rhs0;
			recursively_add_for_coi (aa0, aig, exist_gates, gates);
			
			unsigned aa1 = aa->rhs1;
			recursively_add_for_coi (aa1, aig, exist_gates, gates);
		}
	
		
	}
	
	void Model::add_clauses_from_gate (const aiger_and* aa)
	{
		assert (aa != NULL);
		assert (!is_true (aa->lhs) && !is_false (aa->lhs));
		
		if (is_true (aa->rhs0))
		{
			cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs1)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs1)));
		}
		else if (is_true (aa->rhs1))
		{
			cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs0)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs0)));
		}
		else
		{
			cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs0), -car_var (aa->rhs1)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs0)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs1)));
		}
			
	}
	
		void Model::add_prime_clauses_from_gate (const aiger_and* aa){
		assert (aa != NULL);
		assert (!is_true (aa->lhs) && !is_false (aa->lhs));
		
		if (is_true (aa->rhs0))
		{
			cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs1)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs1)));
			//add the prime for aa->lhs
			cls_.push_back (clause (prime (car_var (aa->lhs)), prime (-car_var (aa->rhs1))));
			cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs1))));
		}
		else if (is_true (aa->rhs1))
		{
			cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs0)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs0)));
			//add the prime for aa->lhs
			cls_.push_back (clause (prime (car_var (aa->lhs)), prime (-car_var (aa->rhs0))));
			cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs0))));
		}
		else
		{
			cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs0), -car_var (aa->rhs1)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs0)));
			cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs1)));
			//add the prime for aa->lhs
			cls_.push_back (clause (prime (car_var (aa->lhs)), prime (-car_var (aa->rhs0)), prime (-car_var (aa->rhs1))));
			cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs0))));
			cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs1))));
		}
	}

	void Model::add_prime_clauses_from_gate_for_coi (const aiger_and* aa){
		assert (aa != NULL);
		assert (!is_true (aa->lhs) && !is_false (aa->lhs));
		
		if (is_true (aa->rhs0))
		{
			coi_cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs1)));
			coi_cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs1)));
			//add the prime for aa->lhs
			coi_cls_.push_back (clause (prime (car_var (aa->lhs)), prime (-car_var (aa->rhs1))));
			coi_cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs1))));
		}
		else if (is_true (aa->rhs1))
		{
			coi_cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs0)));
			coi_cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs0)));
			//add the prime for aa->lhs
			coi_cls_.push_back (clause (prime (car_var (aa->lhs)), prime (-car_var (aa->rhs0))));
			coi_cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs0))));
		}
		else
		{
			coi_cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs0), -car_var (aa->rhs1)));
			coi_cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs0)));
			coi_cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs1)));
			//add the prime for aa->lhs
			coi_cls_.push_back (clause (prime (car_var (aa->lhs)), prime (-car_var (aa->rhs0)), prime (-car_var (aa->rhs1))));
			coi_cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs0))));
			coi_cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs1))));
		}
	}

	// void Model::bmc_add_prime_clauses_from_gate (const aiger_and* aa){
	// 	assert (aa != NULL);
	// 	assert (!is_true (aa->lhs) && !is_false (aa->lhs));
		
	// 	if (is_true (aa->rhs0))
	// 	{
	// 		bmc_cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs1)));
	// 		bmc_cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs1)));
	// 		//add the prime for aa->lhs
	// 		bmc_cls_.push_back (clause (prime (car_var (aa->lhs)), prime (-car_var (aa->rhs1))));
	// 		bmc_cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs1))));
	// 	}
	// 	else if (is_true (aa->rhs1))
	// 	{
	// 		bmc_cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs0)));
	// 		bmc_cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs0)));
	// 		//add the prime for aa->lhs
	// 		bmc_cls_.push_back (clause (prime (car_var (aa->lhs)), prime (-car_var (aa->rhs0))));
	// 		bmc_cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs0))));
	// 	}
	// 	else
	// 	{
	// 		bmc_cls_.push_back (clause (car_var (aa->lhs), -car_var (aa->rhs0), -car_var (aa->rhs1)));
	// 		bmc_cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs0)));
	// 		bmc_cls_.push_back (clause (-car_var (aa->lhs), car_var (aa->rhs1)));
	// 		//add the prime for aa->lhs
	// 		bmc_cls_.push_back (clause (prime (car_var (aa->lhs)), prime (-car_var (aa->rhs0)), prime (-car_var (aa->rhs1))));
	// 		bmc_cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs0))));
	// 		bmc_cls_.push_back (clause (prime (-car_var (aa->lhs)), prime (car_var (aa->rhs1))));
	// 	}
	// }

	void Model::set_init (const aiger* aig)
	{
		for (int i = 0; i < aig->num_latches; i ++)
		{
			if (aig->latches[i].reset == 0)
				init_.push_back (-(num_inputs_+1+i));
			else if (aig->latches[i].reset == 1)
				init_.push_back (num_inputs_+1+i);
			else
			{
				cout << "Error setting initial state!" << endl;
				exit (0);
			}
		}
	}
	
	void Model::set_constraints (const aiger* aig)
	{
		for (int i = 0; i < aig->num_constraints; i ++)
		{
			int id = (int) aig->constraints[i].lit;
			constraints_.push_back ((id%2 == 0) ? (id/2) : -(id/2));
		}
	}
	
	void Model::set_outputs (const aiger* aig)
	{
		for (int i = 0; i < aig->num_outputs; i ++)
		{
			int id = (int) aig->outputs[i].lit;
			outputs_.push_back ((id%2 == 0) ? (id/2) : -(id/2));
		}
	}
	
	int Model::prime (const int id,int level)
	{
		//assert (id != 0 && abs(id) <= max_id_/2);
		
		return (id >= 0 ? (id + (max_id_)*level) : (id - (max_id_)*level));
	}
		
	int Model::previous (const int id,int level){
		assert (abs(id) >= (max_id_)*level);
		
		return (id > 0 ? (id - (max_id_)*level) : (id + (max_id_)*level));
	}
	
	//prime of cls_[id]
	std::vector<int> Model::clause_prime(const int id,int level){
		std::vector<int> res = cls_[id];
		for(int i = 0;i<res.size();i++)
			res[i] = prime(res[i],level-1);
		return res;
	}

	//prime of bmc_cls_[id]
	// std::vector<int> Model::bmc_clause_prime(const int id,int level){
	// 	std::vector<int> res = bmc_cls_[id];
	// 	for(int i = 0;i<res.size();i++)
	// 		res[i] = prime(res[i],level-1);
	// 	return res;
	// }

	//prime of a cube
	void Model::cube_prime(std::vector<int>& cube,int level){
		for(int i = 0;i<cube.size();i++)
			cube[i] = prime(cube[i],level);
	}

	void Model::shrink_to_previous_vars (Cube& uc, bool& constraint,const int unroll_lev){
		int id = max_id ()/2;
		Cube tmp;
		for (auto it = uc.begin(); it != uc.end(); ++it){
			if (id < abs(*it) && (abs(*it) <= prime(max_id(),unroll_lev)))
				tmp.push_back (previous (*it,unroll_lev));
		}
		uc = tmp;
		//for (int i = 0; i < uc.size (); i ++)
			//uc[i] = previous(uc[i]);
	}

	void Model::shrink_to_latch_vars (Cube& uc, bool& constraint)
	{
		Cube tmp;
		constraint = true;
		for (int i = 0; i < uc.size (); i ++)
		{
			if (latch_var (abs (uc[i])))
				tmp.push_back (uc[i]);
			else
				constraint = false;
		}
		uc = tmp;
	}
	
	//propagate the model based on \@ assump, and the results are stored in \@ res
	bool Model::propagate (const std::vector<int>& assump, std::vector<int>& res) {
	    res.resize (max_id_ + 1, 0);
	    for (int i = 0; i < assump.size (); i ++) {
	        res[abs(assump[i])] = assump[i]; 
	    }
	    
	    for (int i = 0; i < cls_.size (); i ++) {
	        Clause& cl = cls_[i];
	        vector<int> tmp;
	        int j = 0;
	        for (; j < cl.size (); j ++) {
	            if (is_true (cl[j]) || res[abs (cl[j])] == cl[j]) {
	                tmp.clear ();
	                break;
	            }
	            if (is_false (cl[j]) || res[abs (cl[j])] == -cl[j]) 
	                continue;
	            tmp.push_back (cl[j]);
	        }
	        if (j >= cl.size ()) {
	            if (tmp.size () == 1) {
	                res[abs(tmp[0])] = tmp[0]; 
	            }
	            //propagate to false
	            else if (tmp.size () == 0) 
	                return false;
	        }
	    }
	    return true;
	}
	
	
	void Model::print ()
	{
	    cout << "-------------------Model information--------------------" << endl;
	    cout << endl << "number of clauses: " << cls_.size () << endl;
	    for (int i  = 0; i < cls_.size (); i ++)
	        car::print (cls_[i]);
		// cout << endl << "number of bmc clauses: " << bmc_cls_.size () << endl;
		// for (int i  = 0; i < bmc_cls_.size (); i ++)
	    //     car::print (bmc_cls_[i]);
	    cout << endl << "next map: " << endl;
	    car::print (next_map_);
	    cout << endl << "reverse next map:" << endl;
	    car::print (reverse_next_map_);
	    cout << endl << "Initial state:" << endl;
	    car::print (init_);
	    cout << endl << "number of Inputs: " << num_inputs_ << endl;
	    cout << endl << "number of Latches: " << num_latches_ << endl;
	    cout << endl << "number of Outputs: " << num_outputs_ << endl;
	    car::print (outputs_);
	    cout << endl << "number of constraints: " << num_constraints_ << endl;
	    car::print (constraints_);
	    cout << endl << "Max id used: " << max_id_ << endl;
	    cout << endl << "outputs start index: " << outputs_start_ << endl;
	    cout << endl << "latches start index: " << latches_start_ << endl;
	    cout << endl << "number of TRUE variables: " << trues_.size () << endl;
	    car::print (trues_); 
	    cout << endl << "-------------------End of Model information--------------------" << endl;   
	}
}
