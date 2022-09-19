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
	Update Date: September 8, 2017
	Interface for the checker class
*/
#include "checker.h"
#include <vector>
#include <iostream>
#include "utility.h"
#include "statistics.h"
pthread_t bmc;
using namespace std;

namespace car
{
    ///////////////////////////////////main functions//////////////////////////////////
    bool Checker::check (std::ofstream& out){
	    for (int i = 0; i < model_->num_outputs (); i ++){
	        if(ilock_)	bad_ = - model_->output (i);
			else bad_ = model_->output (i);
	        
	        //for the particular case when bad_ is true or false
	        if (bad_ == model_->true_id ()){
	        	out << "1" << endl;
	        	out << "b" << i << endl;
	        	if (evidence_){
	        	    //print init state
	        	    out << init_->latches() << endl;
	        	    //print an arbitary input vector
	        	    for (int j = 0; j < model_->num_inputs (); j ++)
	        	        out << "0";
	        	    out << endl;
	        	}
	        	out << "." << endl;
	        	if (verbose_){
	        		cout << "return SAT since the output is true" << endl;
	        	}
	        	return true;
	        }
	        else if (bad_ == model_->false_id ()){
	        	out << "0" << endl;
	        	out << "b" << endl;
	        	out << "." << endl;
	        	if (verbose_){
	        		cout << "return UNSAT since the output is false" << endl;
	        	}
	        	return false;
	        }
	        
	        car_initialization ();
			initialize_sequences ();
	        
			bool bmc_res = false;
			bmc_res = bmc_check();
			
			bool res;
			if(bmc_res) res = true;
			else
			 	res = car_check (); //if time out,use car
			
			
	        if (res)
    			out << "1" << endl;
   			else
    			out << "0" << endl;
    		out << "b" << i << endl;
   			if (evidence_ && res){
				print_evidence (out);
			   }
    			
    		out << "." << endl;
	        car_finalization ();
	        if (i == model_->num_outputs () - 1)
	        	return res;
	    }
	}

	bool Checker::bmc_check(){
		
		if (immediate_satisfiable ()){  //0 step
			return true;
		}
		int unroll = 1;
		double all_bmc_time = 0.0;
		double last_bmc_time = 0.0;
		while (true) {
			clock_t begin = clock();
			if(debug_) std::cout<<"bmc unroll: "<<unroll<<endl;
			unroll_solver_->unroll_one_more(unroll);
			bool res = bmc_sat(unroll);
			if(res){
				//get counterexample
				std::vector<State*> states = bmc_get_all_states(unroll);
				return true;
			}
			else{
				bmc_update_F_sequence(unroll);
			}
			if(bmc_max_time_ < 60){
				clock_t end = clock();
				last_bmc_time = double (end - begin) / CLOCKS_PER_SEC;
				all_bmc_time += last_bmc_time;
				//predict the next bmctime is equal to the last bmctiime, if all + next surpass the max,end
				if((all_bmc_time + last_bmc_time)>= double(bmc_max_time_*60)) return false;
				}
			
			unroll++;
		}
	}

	bool Checker::car_check (){
		if (verbose_)
			cout << "start check ..." << endl;
		if (immediate_satisfiable ()){  //0 step
			if (verbose_)
				cout << "return SAT from immediate_satisfiable" << endl;
			return true;
		}

		//initialize_sequences ();
			
		//int loop_index = 0;
		int loop_index = F_.size()-1;
		while (true){
		    cout << "Frame " << loop_index << endl;
		    //print the number of clauses in each frame
		    for (int i = 0; i < F_.size (); i ++) {
		    	cout << F_[i].size () << " ";
		    }
		    cout << endl;
		    //end of print
		    
		    //handle the special start states
			//reset_start_solver (); //initial state
			// if (!propagate_)
		    // 	clear_frame ();
			minimal_update_level_ = F_.size () - 1;
			if (try_satisfy (loop_index)){
				if (verbose_)
					cout << "return SAT from try_satisfy at frame level " << loop_index << endl;
				return true;
			}
			//it is true when some reason returned from Main solver is empty
			if (safe_reported ()){
				if (verbose_)
					cout << "return UNSAT from safe reported" << endl;
				return false;
			}
			if (propagate_){
				//clear_frame ();
				if (propagate ())
					return false;
			}
			//solver_->print_clauses();
			// if (invariant_found (loop_index)){  //use F size
			// 	if (verbose_){
			// 		cout << "return UNSAT from invariant found at frame " << F_.size ()-1 << endl;
			// 		print ();	
			// 	}
			// 	return false;
			// }
			loop_index += 1;
			
		}
		if (verbose_)
			cout << "end of check" << endl;
		return false;
	}
	
	bool Checker::try_satisfy (const int loop_index)
	{
		
		int res = do_search (loop_index);  //B seq
		if (res == 1)
		    return true;
		else if (res == 0)
		    return false;

		return false;
	}
	
	/*Main function to do state search in CAR
	* Input:
	*       frame_level: The frame level currently working on
	* Output:
	*       1: a counterexample is found
	*       0: The safe result is reported
	*       -1: else
	*/
	int Checker::do_search (const int loop_index) {	
		
		
		if (begin_) {
			vector<State*> states;
			for (int i = 0; i < B_.size (); ++ i) {
				for (int j = 0; j < B_[i].size (); ++ j) 
					states.push_back (B_[i][j]);
			}
			for (int i = 0; i < states.size (); ++ i) {
				if (try_satisfy_by (loop_index, states[i]))
			    	return 1;
				if (safe_reported ())
					return 0;
			}
		}
	
		if (end_) {
	    	for (int i = B_.size () - 1; i >= 0; -- i) {
	        	for (int j = 0; j < B_[i].size (); ++ j) {
			    	if (try_satisfy_by (loop_index, B_[i][j]))
			        	return 1;
					//if (safe_reported ())
				    	//return 0;
			    }
		    }
		}
		   
		return -1;
	}
	
	bool Checker::try_satisfy_by (int loop_index, State* s)
	{
		if (tried_before (s, loop_index+1))
			return false;
		
			
		Configuration c(s,(loop_index),1);
		assert(configurations_.empty());
		configurations_.push_back(c);

		std::set<State*> delete_set;
		while(!configurations_.empty()) //stack non empty
		{

			Configuration config = configurations_.back();
			
			if(debug_){
				std::cout<<"------------"<<endl;
				config.print_config();
			}
				
			if (tried_before (config.get_state(),config.get_frame_level()+config.get_unroll_level() )){
				configurations_.pop_back();
				continue;
			}	

			if(is_sat(config)){
				
				std::vector<State*> states = get_all_states(config); //states in order, the last is the state in config.framelevel
				//push states into stack
				for(int i = 0;i < states.size();++i){
					Configuration temp_c(states[i],config.get_frame_level()+states.size()-i-2,1);
					configurations_.push_back(temp_c);
					update_B_sequence(states[i]);
					//delete_set.insert(states[i]);
					
				}
				if(debug_){
					std::cout<<"is sat"<<endl;
				}

				if(config.get_frame_level() == 0) //exit should be reconsidered
					return true;
	
			}
			else{
				
				configurations_.pop_back();
				update_F_sequence(config); //need add uc invariant check and then block inv
				//if (safe_reported()) return false;
				int unroll_level = config.get_unroll_level();
				int frame_level = config.get_frame_level();
				// if(unroll_level < 4){
				// 	config.set_unroll_level(unroll_level+1);
				// 	configurations_.push_back(config);
				// }
				if(frame_level < loop_index){
					config.set_frame_level(frame_level+1);
					configurations_.push_back(config);
				}	
			}
		}
		return false;
		
	}
	//config helper
	int Checker::get_config_smallest_frame_level(){
		int level = configurations_[0].get_frame_level();
		for(auto i = 1;i < configurations_.size();++i){
			int curr_lev = configurations_[i].get_frame_level();
			if(curr_lev == 0)
				return 0;
			else if(curr_lev < level)
				level = curr_lev;
		}
		return level;
	}
	
	void Checker::push_to_delete_set(){
		for(int i = 0;i < configurations_.size();++i){
			State* current_s = configurations_[i].get_state();
			while(current_s->pre() != NULL){
				current_s->set_skip_delete(true);
				current_s = current_s->pre();
			}
		}
	}

	/*************propagation****************/
	bool Checker::propagate (){
		//int start = forward_ ? (minimal_update_level_ == 0 ? 1 : minimal_update_level_) : minimal_update_level_;
		int start = minimal_update_level_;
		for (int i = (start); i < F_.size()-1; ++i)
			if (propagate (i))
				return true;
		return false;
	}
	
	bool Checker::propagate (int n){
		assert (n >= 0 && n < F_.size()-1);
		Frame& frame = F_[n];
		//Frame& next_frame = (n+1 >= F_.size()) ? frame_ : F_[n+1];
		Frame& next_frame = F_[n+1];
		bool flag = true;
		for (int i = 0; i < frame.size (); ++i){
			Cube& cu = frame[i];
			
			
			bool propagated = false;
			for (int j = 0; j < next_frame.size(); ++j){
				if (car::imply (cu, next_frame[j]) && car::imply (next_frame[j], cu)){
					propagated = true;
					break;
				}
			}
			if (propagated) continue;
			
	
		    if (propagate (cu, n)){
		    	push_to_frame (cu, n+1,0);
		    }
		    else
		    	flag = false;
		}
		
		if (flag)
			return true;
		return false;
	}
	
	bool Checker::propagate (Cube& cu, int n){
		solver_->set_assumption (cu, n, forward_,1);
		//solver_->print_assumption();
		//solver_->print_clauses();
	    stats_->count_main_solver_SAT_time_start ();
		bool res = solver_->solve_with_assumption ();
		stats_->count_main_solver_SAT_time_end ();
		if (!res)
			return true;
		return false;
	}
	
		
	//////////////helper functions/////////////////////////////////////////////

	Checker::Checker (Model* model, Statistics& stats, ofstream* dot, bool forward, bool evidence, bool partial, bool propagate, bool begin, bool end, bool inter, bool rotate, bool verbose, bool minimal_uc, bool ilock,int unroll_max,bool debug,int bmc_max_time)
	{
	    
		model_ = model;
		stats_ = &stats;
		dot_ = dot;
		solver_ = NULL;
		unroll_solver_ = NULL;
		lift_ = NULL;
		dead_solver_ = NULL;
		start_solver_ = NULL;
		inv_solver_ = NULL;
		init_ = new State (model_->init ());
		last_ = NULL;
		forward_ = forward;
		safe_reported_ = false;
		minimal_uc_ = minimal_uc;
		ilock_ = ilock;
		unroll_max_ = unroll_max;
		bmc_max_time_= bmc_max_time;
		debug_ = debug; 
		evidence_ = evidence;
		verbose_ = verbose;
		minimal_update_level_ = F_.size ()-1;
		solver_call_counter_ = 0;
		start_solver_call_counter_ = 0; 
		partial_state_ = partial;
		dead_flag_ = false;
		//set propagate_ to be true by default
		propagate_ = propagate;
		
		begin_ = begin;
		end_ = end;
		inter_ = inter;
		rotate_ = rotate;
		frame_.resize(unroll_max);
	}
	Checker::~Checker ()
	{
		/*
		if (init_ != NULL)
		{
			delete init_;
			init_ = NULL;
		}
		if (last_ != NULL)
		{
		    delete last_;
		    last_ = NULL;
		}
		*/
		//car_finalization ();
	}
	
	void Checker::destroy_states ()
	{    
	    for (int i = 0; i < B_.size (); i ++)
	    {
	    	//cout << "B[" << i << "]:" <<endl;
	        for (int j = 0; j < B_[i].size (); j ++)
	        {
	        	if (B_[i][j] != NULL)
	        	{
	        		//car::print (B_[i][j]->s());
	            	delete B_[i][j];
	            	B_[i][j] = NULL;
	            }
	        }
	    }
	    B_.clear ();
	}
	
	void Checker::car_initialization ()
	{
	    solver_ = new MainSolver (model_, stats_, verbose_);
		unroll_solver_ = new MainSolver (model_, stats_, verbose_,true);
		inv_solver_ = new InvSolver (model_);
	    if (forward_){
	    	lift_ = new MainSolver (model_, stats_, verbose_);
	    	dead_solver_ = new MainSolver (model_, stats_, verbose_);
	    	dead_solver_->add_clause (-bad_);
	    }
		start_solver_ = new StartSolver (model_, bad_, forward_, verbose_);
		assert (F_.empty ());
		assert (B_.empty ());
		
	}
	
	void Checker::car_finalization ()
	{
		// for (int i = 0; i < F_.size(); ++i){
		// 	cout << "Frame " << i << endl;
		// 	for (int j = 0; j < F_[i].size(); ++j)
		// 		car::print (F_[i][j]);
		// }
	
		
	    F_.clear ();
		configurations_.clear ();
	    destroy_states ();
	    if (solver_ != NULL) {
	        delete solver_;
	        solver_ = NULL;
	    }
		if (unroll_solver_ != NULL) {
	        delete unroll_solver_;
	        unroll_solver_ = NULL;
	    }
	    if (lift_ != NULL) {
	        delete lift_;
	        lift_ = NULL;
	    }
	    if (dead_solver_ != NULL) {
	        delete dead_solver_;
	        dead_solver_ = NULL;
	    }
	    if (start_solver_ != NULL) {
	        delete start_solver_;
	        start_solver_ = NULL;
	    }
	}
	
	
	bool Checker::immediate_satisfiable ()
	{
	    bool res = solver_solve_with_assumption (init_->s (), bad_);
	    if (res)
	    {
	        Assignment st = solver_->get_model ();
	        std::pair<Assignment, Assignment> pa = state_pair (st);
	        if (forward_)
	            init_->set_inputs (pa.first);
	        else
	            last_ = new State (NULL, pa.first, pa.second, forward_, true);
	        
	        return true;
	    }

	    return false;
	}
	
	void Checker::initialize_sequences ()
	{
		//F inital
		Frame frame;
		Cube temp;
		temp.push_back(bad_);
	    frame.push_back(temp);
		F_.push_back(frame);

		//B initial
		std::vector<State*> v;
		v.push_back(init_);
		B_.push_back(v);

		Cube& cu = init_->s();
		cubes_.push_back (cu);
	}
	
		
	State* Checker::enumerate_start_state ()
	{
		while (true)
		{
			//start_solver_->print_assumption ();
	    	//start_solver_->print_clauses ();
	    	bool val = start_solver_solve_with_assumption ();

			if (val)  
			{
				State* res = get_new_start_state ();
				return res;
			}
			else
				break;
		}
		
		return NULL;
	}
	
	State* Checker::get_new_start_state ()
	{
		Assignment st = start_solver_->get_model ();
		assert (st.size() >= model_->num_inputs() + model_->num_latches());
		st.resize (model_->num_inputs() + model_->num_latches());
		if (partial_state_)
			get_partial (st);
		std::pair<Assignment, Assignment> pa = state_pair (st);
		State *res = new State (NULL, pa.first, pa.second, forward_, true);
		return res;
	}
	
	std::pair<Assignment, Assignment> Checker::state_pair (const Assignment& st)
	{
		Assignment inputs, latches;
		if (!partial_state_){
	    	assert (st.size () >= model_->num_inputs () + model_->num_latches ());
	    	for (int i = 0; i < model_->num_inputs (); i ++)
	        	inputs.push_back (st[i]);
	    	for (int i = model_->num_inputs (); i < st.size (); i ++)
	    	{
	        	if (abs (st[i]) > model_->num_inputs () + model_->num_latches ())
	            	break;
	        	latches.push_back (st[i]);
	    	}
	    }
	    else{
	    	for (auto it = st.begin(); it != st.end (); ++it){
	    		if (abs(*it) <= model_->num_inputs ())
	    			inputs.push_back (*it);
	    		else if (abs(*it) <= model_->num_inputs () + model_->num_latches ())
	    			latches.push_back (*it);
	    	}
	    }
	    return std::pair<Assignment, Assignment> (inputs, latches);
	}
	
	
	
	bool Checker::immediate_satisfiable (const State* s)
	{
	    if (forward_)
	    {//s is actually the initial state
	    	init_->set_inputs (const_cast<State*> (s)->inputs_vec ());
	    	init_->set_next (const_cast<State*> (s)->next ());
	        return true;
	    }
	    else
	    {
	        bool res = solver_solve_with_assumption (const_cast<State*> (s)-> s(), bad_);
	        if (res)
	        {//s is actually the last_ state
	            Assignment st = solver_->get_model ();
	            std::pair<Assignment, Assignment> pa = state_pair (st);
	            const_cast<State*> (s)->set_last_inputs (pa.first);
	            last_ = new State (const_cast<State*>(s));
	            last_->set_final (true);
	            //////generate dot data
	            if (dot_ != NULL)
	                (*dot_) << "\n\t\t\t" << last_->id () << " [shape = circle, color = red, label = \"final\", size = 0.01];";
	            //////generate dot data
	            return true;
	        }
	        return false;
	    }
	}
	
	//a copy for cube
	bool Checker::immediate_satisfiable (const Cube& cu)
	{
	    if (forward_)
	    {
	        return true;
	    }
	    else
	    {
	        bool res = solver_solve_with_assumption (cu, bad_);
	        return res;
	    }
	}
	
	bool Checker::invariant_found (int& inv_index)
	{
		int frame_level = inv_index;
		bool res = false;
		create_inv_solver ();
		for (int i = 0; i < frame_level; i ++)
		{
			if (invariant_found_at (i))
			{
				res = true;
				//delete frames after i, and the left F_ is the invariant
				while (F_.size () > i+1)
					F_.pop_back ();
				//cout << "invariant found at frame " << i << endl;
				break;
			}
		}
		delete_inv_solver ();
		return res;
	}
	
	//irrelevant with the direction, so don't care forward or backward
	bool Checker::invariant_found_at (const int frame_level) 
	{

		if (frame_level <= minimal_update_level_){
			inv_solver_add_constraint_or (frame_level);
			return false;
		}
		inv_solver_add_constraint_and (frame_level);

		//inv_solver_->print_assumption ();
		//inv_solver_->print_clauses();	
		stats_->count_inv_solver_SAT_time_start ();
		bool res = !inv_solver_->solve_with_assumption ();
		stats_->count_inv_solver_SAT_time_end ();
		inv_solver_release_constraint_and ();
		inv_solver_add_constraint_or (frame_level);
		return res;
	}
	
	
	void Checker::inv_solver_add_constraint_or (const int frame_level)
	{
		//add \bigcup F_i (\bigcup B_i)
		inv_solver_->add_constraint_or (F_[frame_level], forward_);
	}
	
	void Checker::inv_solver_add_constraint_and (const int frame_level)
	{
		//add \neg F_{frame_level} (\neg B_{frame_level})
		inv_solver_->add_constraint_and (F_[frame_level], forward_);
	}
	
	void Checker::inv_solver_release_constraint_and ()
	{
		inv_solver_->release_constraint_and ();
	}
	
	// bool Checker::solve_with (const Cube& s, const int frame_level)
	// {
	// 	if (frame_level == -1)
	// 		return immediate_satisfiable (s);
				
	// 	bool res = solver_solve_with_assumption (s, frame_level, forward_);
		
	// 	return res;
	// }
	
	
	
	State* Checker::get_new_state (const State* s,const int unroll_lev)
	{
		
		Assignment st = solver_->get_state (forward_, partial_state_);
		//st includes both input and latch parts
		// if (partial_state_ && unroll_lev==1)
		// 	get_partial (st, s);
		std::pair<Assignment, Assignment> pa = state_pair (st);
		State* res = new State (s, pa.first, pa.second, forward_,false,unroll_lev);
		
		return res;
	}

	std::vector<State*> Checker::get_all_states(Configuration& config){
		int unroll_lev = config.get_unroll_level();
		State* s = config.get_state();
		Cube first_input;
		std::vector<Cube> st_vec;
		if(unroll_lev == 1)
			st_vec = solver_->get_state_vector (unroll_lev,first_input);
		else
			st_vec = unroll_solver_->get_state_vector (unroll_lev,first_input);;
		std::vector<State*> res;
		std::pair<Assignment, Assignment> pa = state_pair (st_vec[0]);
		State* first_s = new State (s, first_input, pa.second, forward_,false,1); //get the first 
		res.push_back(first_s);
		for (int ind = 1;ind < st_vec.size();++ind){
			Cube input = pa.first;
			pa = state_pair (st_vec[ind]);
			State* new_s = new State (first_s, input, pa.second, forward_,false,ind+1);
			res.push_back(new_s);
			first_s = new_s;
		}

		if (config.get_frame_level() == 0){
			last_ = res.back();
			last_->set_last_inputs(pa.first);
		}
		
		return res;
	}

	std::vector<State*> Checker::bmc_get_all_states(int unroll_lev){
		
		State* s = init_;
		Cube first_input;
		std::vector<Cube> st_vec = unroll_solver_->get_state_vector (unroll_lev,first_input);;
		std::vector<State*> res;
		std::pair<Assignment, Assignment> pa = state_pair (st_vec[0]);
		State* first_s = new State (s, first_input, pa.second, forward_,false,1); //get the first 
		res.push_back(first_s);
		for (int ind = 1;ind < st_vec.size();++ind){
			Cube input = pa.first;
			pa = state_pair (st_vec[ind]);
			State* new_s = new State (first_s, input, pa.second, forward_,false,ind+1);
			res.push_back(new_s);
			first_s = new_s;
		}
		last_ = res.back();
		last_->set_last_inputs(pa.first);
		return res;
	}
	
	void Checker::get_partial (Assignment& st, const State* s){
		if (!forward_) 
			return;
		Cube assumption = st;
		if (s != NULL){
			Cube& cube = s->s();
			Clause cl;
			for (auto it = cube.begin(); it != cube.end(); ++it)
				cl.push_back (-model_->prime (*it));
			int flag = lift_->new_flag ();
			cl.push_back (flag);
			lift_->add_clause (cl);
		
			assumption.push_back (-flag);
			bool ret = lift_->solve_with_assumption (assumption);
			//lift_->print_assumption ();
			//lift_->print_clauses ();
		
			assert (!ret);
			bool constraint = false;
			st = lift_->get_conflict (!forward_, minimal_uc_, constraint);
			if (st.empty()){
			//every state can reach s, thus make st the initial state.
				st = init_->s();
				return;
			}
			
		///?????????????????
			lift_->add_clause (-flag);	
			//lift_->print_clauses ();
		}
		else{
			assumption.push_back (-bad_);
			//lift_->print_clauses();
			bool ret = lift_->solve_with_assumption (assumption);
			assert (!ret);
			bool constraint = false;
			st = lift_->get_conflict (!forward_, minimal_uc_, constraint);
		
			//remove -bad_
			for (auto it = st.begin(); it != st.end(); ++it){
				if (*it == -bad_){
					st.erase (it);
					break;
				}
			}
			
			assert (!st.empty());
		}
	}
	
	
	void Checker::extend_F_sequence ()
	{
		for(int lev = 0;lev<unroll_max_;lev++){
		F_.push_back (frame_[lev]);
		solver_->add_new_frame (frame_[lev], F_.size()+lev-1, forward_);
		}
		cubes_.push_back (cube_);
		comms_.push_back (comm_);
		
	}
	
	void Checker::update_B_sequence (State* s)
	{
	    while (int (B_.size ()) <= s->depth ())
	    {
	        vector<State*> v;
	        B_.push_back (v);
	    }
		
	    B_[s->depth ()].push_back (s);
	}
	
	void Checker::update_F_sequence (Configuration& config)
	{	
		int unroll_lev = config.get_unroll_level();
		int frame_level = config.get_frame_level();
		
		bool constraint = false;
		Cube cu;
		if(unroll_lev == 1)
			cu = solver_->get_conflict (forward_, minimal_uc_, constraint, unroll_lev);
		else
		 	cu = unroll_solver_->get_conflict (forward_, minimal_uc_, constraint, unroll_lev);
		if(debug_){
			cout<<"add uc:"<<endl;
			car::print(cu);
		}
		// if(uc_inv_check(cu)){
		// 	Cube new_cu = inv_solver_->get_conflict();
		// 	if(debug_){
		// 		cout<<"find inv uc:";
		// 		car::print(new_cu);
		// 	}
		// 	inv_cube.push_back(new_cu);
		// 	solver_->CARSolver::add_clause_from_cube(new_cu);
		// 	for(int i = 1;i <= unroll_max_;++i){
		// 		Cube tmp;
		// 		for(auto it = new_cu.begin();it != new_cu.end();++it){
		// 			tmp.push_back(model_->prime(*it,i));
		// 		}
		// 		solver_->CARSolver::add_clause_from_cube(tmp);
		// 	}
		// 	return ;
		// }	
	
		
		if(cu.empty()){
			report_safe ();
		}
		
	
		if (safe_reported ())
		{
			return;
		}

		push_to_frame (cu, frame_level, unroll_lev);
		
	}
	
	void Checker::bmc_update_F_sequence (int unroll_lev)
	{	
		
		int frame_level = 0;
		
		bool constraint = false;
		Cube cu = unroll_solver_->get_conflict (forward_, minimal_uc_, constraint, unroll_lev);

		if(cu.empty()){
			report_safe ();
		}
	
		if (safe_reported ())
		{
			return;
		}

		Frame new_frame;
		new_frame.push_back(cu);
		F_.push_back(new_frame);

		solver_->add_clause_from_cube (cu, unroll_lev, forward_);
		
		
	}

	bool Checker::is_dead (const State* s, Cube& dead_uc){
	
		Cube assumption;
		
		Cube common;
		if (deads_.size() > 0) 
			common = car::cube_intersect (deads_[deads_.size()-1], s->s());
			
		for (auto it = common.begin(); it != common.end(); ++it)
			assumption.push_back (forward_ ? model_->prime (*it) : (*it));
			
		for (auto it = s->s().begin(); it != s->s().end(); ++it)
			assumption.push_back (forward_ ? model_->prime (*it) : (*it));
		
		/*
		Cube common;
		if (deads_.size() > 0) 
			common = car::cube_intersect (deads_[deads_.size()-1], s->s());
		for (auto it = common.begin(); it != common.end(); ++it)
			assumption.push_back (forward_ ? model_->prime (*it) : (*it));
		//assumption.insert (assumption.begin (), common.begin (), common.end ());
		*/
		
		
		/*
		if (!s->added_to_dead_solver ()){
			dead_solver_->CARSolver::add_clause_from_cube (s->s());
			s->set_added_to_dead_solver (true);
		}
		*/
			
		bool res = dead_solver_->solve_with_assumption (assumption);
		if (!res){
			bool constraint = false;
			dead_uc = dead_solver_->get_conflict (forward_, minimal_uc_, constraint);
			//foward dead_cu MUST rule out those not in \@s //TO BE REUSED!
			if (forward_){
				Cube tmp;
				Cube &st = s->s();
				if (!partial_state_){
					for(auto it = dead_uc.begin(); it != dead_uc.end(); ++it){
						int latch_start = model_->num_inputs()+1;
						if (st[abs(*it)-latch_start] == *it)
							tmp.push_back (*it);
					}
				}
				else{
					hash_set<int> tmp_set;
					for (auto it = st.begin (); it != st.end(); ++it)
						tmp_set.insert (*it);
					for (auto it = dead_uc.begin(); it != dead_uc.end(); ++it){
						if (tmp_set.find (*it) != tmp_set.end())
							tmp.push_back (*it);
					}
				}
				dead_uc = tmp;
				
				/*
				//shrink dead_uc
				while (dead_uc.size() != assumption.size()){
					assumption.clear ();
					for (auto it = dead_uc.begin(); it != dead_uc.end(); ++it)
						assumption.push_back (forward_ ? model_->prime (*it) : (*it));
						
					dead_solver_->CARSolver::add_clause_from_cube (dead_uc);
					
					res = dead_solver_->solve_with_assumption (assumption);
					assert (!res);
					
					constraint = false;
					Cube last_dead_uc = dead_uc;
					dead_uc = dead_solver_->get_conflict (forward_, minimal_uc_, constraint);
					//foward dead_cu MUST rule out those not in \@s //TO BE REUSED!
					Cube tmp;
					Cube &st = last_dead_uc;
					hash_set<int> tmp_set;
					for (auto it = st.begin (); it != st.end(); ++it)
						tmp_set.insert (*it);
					for (auto it = dead_uc.begin(); it != dead_uc.end(); ++it){
						if (tmp_set.find (*it) != tmp_set.end())
							tmp.push_back (*it);
					}

					dead_uc = tmp;
				}
				*/
			}
			assert (!dead_uc.empty());
		}
		else{
			if (!s->added_to_dead_solver ()){
				dead_solver_->CARSolver::add_clause_from_cube (s->s());
				s->set_added_to_dead_solver (true);
			}
		}
		return !res;
	}
	
	void Checker::add_dead_to_inv_solver (){
		for (auto it = deads_.begin (); it != deads_.end(); ++it){
			Clause cl;	
			for (auto it2 = (*it).begin(); it2 != (*it).end (); ++it2){
				cl.push_back (forward_? -(*it2) : -model_->prime(*it2));
			}
		
			if (is_initial (*it)){
				//create dead clauses : MUST consider the initial state not excluded by dead states!!!
				std::vector<Clause> cls;
				int init_flag = inv_solver_->new_var ();
				int dead_flag = inv_solver_->new_var ();
				if (true){//not consider initial state yet
					Clause cl2;
					
					cl2.push_back (init_flag);
					cl2.push_back (dead_flag);
					cls.push_back (cl2);
					//create clauses for I <- inv_solver_->init_flag
					for (auto it2 = init_->s().begin(); it2 != init_->s().end(); ++it2){
						cl2.clear ();
						cl2.push_back (init_flag);
						cl2.push_back (*it2);
						cls.push_back (cl2);
					}
				}
				//create clauses for !dead <-inv_solver->dead_flag
				cl.push_back (dead_flag);
				cls.push_back (cl);
		
				for (auto it2 = cls.begin(); it2 != cls.end(); ++it2){
					inv_solver_->add_clause (*it2);
				}
			}
			else
				inv_solver_->add_clause (cl);
		}
	}
	
	void Checker::add_dead_to_solvers (Cube& dead_uc){
		std::vector<Cube> tmp_deads;
		for (auto it = deads_.begin (); it != deads_.end (); ++it){
			if (!imply (*it, dead_uc))
				tmp_deads.push_back (*it);
		}
		deads_ = tmp_deads;
		deads_.push_back (dead_uc);
		//car::print (dead_uc);
		
		Clause cl;	
		for (auto it = dead_uc.begin(); it != dead_uc.end (); ++it){
			cl.push_back (forward_? -(*it) : -model_->prime(*it));
		}
		start_solver_->add_clause (cl);
		
		if (is_initial (dead_uc)){
			//create dead clauses : MUST consider the initial state not excluded by dead states!!!
			std::vector<Clause> cls;
			if (!dead_flag_){//not consider initial state yet
				Clause cl2;
				cl2.push_back (solver_->init_flag());
				cl2.push_back (solver_->dead_flag());
				cls.push_back (cl2);
				//create clauses for I <- solver_->init_flag()
				for (auto it = init_->s().begin(); it != init_->s().end(); ++it){
					cl2.clear ();
					cl2.push_back (-solver_->init_flag());
					cl2.push_back (*it);
					cls.push_back (cl2);
				}
				dead_flag_ = true;
			}
			//create clauses for !dead <-solver_->dead_flag()
			cl.push_back (-solver_->dead_flag());
			cls.push_back (cl);
		
			for (auto it = cls.begin(); it != cls.end(); ++it){
				solver_->add_clause (*it);
				lift_->add_clause (*it);
				dead_solver_->add_clause (*it);
			}
		}
		else{
			solver_->add_clause (cl);
			lift_->add_clause (cl);
			dead_solver_->add_clause (cl);
		}
			
	}
	
	Cube Checker::get_uc (Cube &c) {
		bool constraint = false;
		Cube cu = solver_->get_conflict (forward_, minimal_uc_, constraint);
		    
		//foward cu MUST rule out those not in \@s
		Cube tmp;
		//Cube &st = s->s();
		for(auto it = cu.begin(); it != cu.end(); ++it){
			if (car::is_in (*it, c, 0, c.size()-1))
				tmp.push_back (*it);
		}
		cu = tmp;
			
		//pay attention to the size of cu!
		if (cu.empty ())
		{
			report_safe ();
			//return cu;
		}
		return cu;
	}

	
	void Checker::push_to_frame (Cube& cu, const int frame_level,int unroll_level)
	{
		//to be done
		//Frame& frame = (frame_level < int (F_.size ())) ? F_[frame_level] : frame_[unroll_level-1];
		assert(frame_level+unroll_level <= F_.size ());
		if(frame_level+unroll_level == F_.size ()){
			Frame new_frame;
			new_frame.push_back(cu);
			F_.push_back(new_frame);
		}	
		else{
			Frame& frame = F_[frame_level+unroll_level];
			//To add \@ cu to \@ frame, there must be
			//1. \@ cu does not imply any clause in \@ frame
			//2. if a clause in \@ frame implies \@ cu, replace it by \@cu
			Frame tmp_frame;
			stats_->count_clause_contain_time_start ();
			for (int i = 0; i < frame.size (); i ++)
			{   
				if (forward_){//for incremental
					if (imply (cu, frame[i]))
						return;
				}
				if (!imply (frame[i], cu))
					tmp_frame.push_back (frame[i]);	
				else {
					stats_->count_clause_contain_success ();
				}
			} 
			stats_->count_clause_contain_time_end ();
			tmp_frame.push_back (cu);
			
			frame = tmp_frame;

		}
		
		if (frame_level+unroll_level-1 < minimal_update_level_)
			minimal_update_level_ = frame_level+unroll_level;
		
		solver_->add_clause_from_cube (cu, frame_level+unroll_level, forward_);
		// cout<<"frame_lev: "<<frame_level+unroll_level<<endl;
		// car::print(cu);
		//to be done
		// else if (frame_level == int (F_.size ()))
		// 	start_solver_->add_clause_with_flag (cu);
	}
	
	
	int Checker::get_new_level (const State *s, const int frame_level){
	    for (int i = 0; i < frame_level; i ++){
	        int j = 0;
	        for (; j < F_[i].size (); j ++){
	        	bool res = partial_state_ ? car::imply (s->s(), F_[i][j]) : s->imply (F_[i][j]);
	            if (res)
	                break;
	        }
	        if (j >= F_[i].size ())
	            return i-1;
	    }
		return frame_level - 1;
	}
	
	bool Checker::tried_before (const State* st, const int frame_level) {
		
		//end of check
		if (F_.size() <= frame_level)
			return false;
	    assert (frame_level >= 0);
	    //Frame &frame = (frame_level < F_.size ()) ? F_[frame_level] : frame_[frame_level-F_.size()];
		Frame &frame = F_[frame_level];
	    
		stats_->count_state_contain_time_start ();
		for (int i = 0; i < frame.size (); i ++) {
			if (car::imply (st->s(), frame[i])) {
				stats_->count_state_contain_time_end ();
				return true;
			} 
		}
		stats_->count_state_contain_time_end ();
	    
	   
	    
	    return false;
	}
	
	
	void Checker::get_previous (const Assignment& st, const int frame_level, std::vector<int>& res) {
	    if (frame_level == -1) return;
	    Frame& frame = (frame_level < F_.size ()) ? F_[frame_level] : frame_[frame_level-F_.size()];
	    
	    for (int i = frame.size ()-1; i >= 0; --i) {
	        Cube& cu = frame[i];
	        int j = 0;
	        for (; j < cu.size() ; ++ j) {
	    	    if (st[abs(cu[j])-model_->num_inputs ()-1] != cu[j]) {
	    		    break;
	    	    }
	        }
	        if (j >= cu.size ()) { 
	            res = cu;
	            break;
	        }
	    }
	}
	
	//collect priority ids and store in \@ res
	void Checker::get_priority (const Assignment& st, const int frame_level, std::vector<int>& res) {
	    
	    //get_previous (st, frame_level, res);
	    
	    //Frame& frame = (frame_level+1 < F_.size ()) ? F_[frame_level+1] : frame_[frame_level-F_.size()];
	    Frame& frame =  F_[frame_level+1];
		if (frame_level >= F_.size()-1 || frame.size () == 0)  
	    	return;
	    	
	    Cube& cu = frame[frame.size()-1];
	        
	    std::vector<int> tmp;
	    tmp.reserve (cu.size());
	    if(!forward_){
	    	for (int i = 0; i < cu.size() ; ++ i) {
	    		if (st[abs(cu[i])-model_->num_inputs ()-1] == cu[i]) {
	    			tmp.push_back (cu[i]);
	    		}
	    	}
	    	res = tmp;
	    }
	    else{
	    	res = car::cube_intersect (cu, st);
	    }
	    //res.insert (res.begin (), tmp.begin (), tmp.end ());
	}
	
	//add the intersection of the last UC in frame_level+1 with the state \@ st to \@ st
	void Checker::add_intersection_last_uc_in_frame_level_plus_one (Assignment& st, const int frame_level) {

	    std::vector<int> prefix;
	    if (inter_) 
	    	get_priority (st, frame_level, prefix);	
	    
	    if (rotate_) { 	    
	    std::vector<int> tmp_st, tmp;
	    tmp_st.reserve (st.size());
	    tmp.reserve (st.size());
	    //Cube& cube = (frame_level+1 < cubes_.size ()) ? cubes_[frame_level+1] : cube_;
		if (frame_level+1 >= cubes_.size ()) return;
		Cube& cube = cubes_[frame_level+1];
	    if (cube.empty ()) {
	        //cube = st;
	        return;
	    }
	    for (int i = 0; i < cube.size (); ++ i) {
	        if (st[abs(cube[i])-model_->num_inputs ()-1] == cube[i]) 
	    		tmp_st.push_back (cube[i]);
	    	else
	    	    tmp.push_back (-cube[i]);
	    }
	    
	    for (int i = 0; i < tmp.size (); ++ i)
	        tmp_st.push_back (tmp[i]);
	        
	    st = tmp_st;
	    //cube = st;
	    }
	    
	    st.insert (st.begin (), prefix.begin (), prefix.end ());
	  
           /* 
            Cube& comm = (frame_level+1 < comms_.size ()) ? comms_[frame_level+1] : comm_;
	    vector<int> tmp_comm;
	    tmp_comm.reserve (comm.size ());
	    for (int i = 0; i < comm.size (); ++ i) {
	        if (st[abs(comm[i])-model_->num_inputs ()-1] == comm[i]) 
	    		tmp_comm.push_back (comm[i]);
	    }
            st.insert (st.begin (), tmp_comm.begin(), tmp_comm.end ());
	*/
	}
	void Checker::print_evidence (ofstream& out) {
		if (forward_)
			init_->print_evidence (forward_, out);
		else
			last_->print_evidence (forward_, out);
	}
		
	// void Checker::print_evidence (ofstream& out) {
	// 	out<<init_->latches()<<endl;
	// 	for (int i = 0;i < configurations_.size();++i){
	// 		State* s = configurations_[i].get_state();
	// 		out<<s->inputs()<<endl;
	// 	}	
	// }

	// void Checker::push_unrollpair_to_frame(){
	// 	for (auto it = unroll_pair.begin();it != unroll_pair.end();++it){
	// 		if((*it).second < F_.size()){
	// 			//cout<<"push success"<<endl;
	// 			push_to_frame((*it).first,(*it).second);
	// 			unroll_pair.erase(it);
	// 		} 
	// 	}
	// }

}
