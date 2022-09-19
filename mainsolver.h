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
	Update Date: October 6, 2017
	Main Solver in CAR
*/

#ifndef MAIN_SOLVER_H
#define MAIN_SOLVER_H

#include "carsolver.h"
#include "data_structure.h"
#include "model.h"
#include "statistics.h"
#include <utility>
#include <vector>
#include <map>
#include <assert.h>
#include <iostream>

namespace car{

typedef std::pair<int,int> Frame_unroll_pair;

class MainSolver : public CARSolver 
{
	public:
		MainSolver (Model*, Statistics* stats, const bool verbose = false);
		MainSolver (Model* m, Statistics* stats, const bool verbose, const bool unroll);
		~MainSolver (){}
		
		//public funcitons
		void set_assumption (const Assignment&, const int bad,const int frame_level, const bool forward);
		void set_assumption (const Assignment&, const int bad,const int frame_level, const bool forward,const int unroll_lev);
		void set_assumption (const Assignment&, const int);
		void bmc_set_assumption (const Assignment& a,const int bad,const int unroll_level);
		void set_assumption (const Assignment& st){
			assumption_.clear ();
			for (auto it = st.begin(); it != st.end(); ++it)
				assumption_push (*it);
		}

		void unroll_one_more(const int level);
		void unroll_to_level(const int level);

		inline int get_unroll_flag(int& ind) {return unroll_flags_[ind-2];}
		inline int get_unroll_level(){return current_unroll_level_;}

		inline bool solve_with_assumption (const Assignment& st, const int p)
		{
		    set_assumption (st, p);
		    if (verbose_)
		    	std::cout << "MainSolver::";
		    return solve_assumption ();
		}
		
		inline bool solve_with_assumption (const Assignment& st)
		{
		    set_assumption (st);
		    if (verbose_)
		    	std::cout << "MainSolver::";
		    return solve_assumption ();
		}
		
		inline bool solve_with_assumption ()
		{
			if (verbose_)
		    	std::cout << "MainSolver::";
		    return solve_assumption ();
		}
		
		Assignment get_state (const bool forward = true, const bool partial = false);
		std::vector<Cube> get_state_vector (int unroll_level,Cube& first_input);
		
		//this version is used for bad check only
		Cube get_conflict (const int bad);
		Cube get_conflict (const bool forward, const bool minimal, bool& constraint,const int unroll_lev=1);
		
		void add_new_frame (const Frame& frame, const int frame_level, const bool forward);
		//overload
		void add_clause_from_cube (const Cube& cu, const int frame_level, const bool forward_);

		void push_frame_to_unroll_solver(const Frame& frame,const int& frame_level,const int& unroll_level);

		bool solve_with_assumption_for_temporary (Cube& s, int frame_level, bool forward, Cube& tmp_block);
		
		inline void update_constraint (Cube& cu)
		{
		    CARSolver::add_clause_from_cube (cu);
		}
		
		
		inline int new_flag (){
			return max_flag_++;
		}
		
		inline int init_flag () {return init_flag_;}
		inline int dead_flag () {return dead_flag_;}
		
	private:
		//members
		int max_flag_;
		//std::vector<int> frame_flags_;
		//std::vector<Cube> frame_flags_; //frame unroll flag

		std::vector<int> frame_flag_;
		std::map<Frame_unroll_pair,int> frame_unroll_flag_map_;
		std::map<Frame_unroll_pair,int> frame_unroll_level_map_; // <frame,unroll> has add how many cubes in frame
		int init_flag_, dead_flag_;
		
		Model* model_;
		
		Statistics* stats_;
		
		int current_unroll_level_;
		int max_unroll_level_;
		std::vector<int> unroll_flags_; //flags for each unroll level
		
		//bool verbose_;
		
		//functions
		
		inline int flag_of (const unsigned frame_level) 
		{
		    assert (frame_level > 0);
			while (frame_level > frame_flag_.size ())
			{
				frame_flag_.push_back(max_flag_++);
			}
			return frame_flag_[frame_level-1];
		}
		
		
		// inline int flag_of (const unsigned frame_level,const int unroll_level=1) 
		// {
		//     assert (frame_level > 0);
		// 	while (frame_level > frame_flags_.size ())
		// 	{
		// 		Cube tmp;
		// 		for(int i=0;i<max_unroll_level_;++i)
		// 			tmp.push_back(max_flag_++);
		// 		frame_flags_.push_back (tmp);
		// 	}
	        
		// 	return frame_flags_[frame_level-1][unroll_level-1];
		// }
		void shrink_model (Assignment& model, const bool forward, const bool partial);
		std::vector<Cube> shrink_model_vector (Assignment& model,int unroll_level,Cube& first_input);
		void try_reduce (Cube& cu);
};

}

#endif

