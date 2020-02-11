#pragma once

#include "preprocessorinterface.hpp"
#include "../cadical/src/cadical.hpp"
#include "PriorityQueue.h"

#include <iostream>
#include <fstream>
#include <sstream>
#include <cstdlib>
#include <cmath>
#include <cstring>
#include <queue>
#include <set>
#include <stdio.h>
#include <stdlib.h>
#include <vector>

#include <sys/times.h> //these two h files are for timing in linux
#include <unistd.h>

using namespace std;

#define mypop(stack) stack[--stack ## _fill_pointer]
#define mypush(item, stack) stack[stack ## _fill_pointer++] = item

const float MY_RAND_MAX_FLOAT = 10000000.0;
const int   MY_RAND_MAX_INT   = 10000000;
const float BASIC_SCALE       = 0.0000001; //1.0f/MY_RAND_MAX_FLOAT;

// Define a data structure for a literal.
struct lit
{
    int  clause_num; //clause num, begin with 0
    int  group_num;  //group num of clause, begin with 1
    int  var_num;    //variable num, begin with 1
    bool sense;      //is 1 for true literals, 0 for false literals.
};


bool sort_lit_by_group(lit a, lit b);

bool sort_lit_by_group(lit a, lit b)
{
    return a.group_num < b.group_num;
}

static struct tms start_time;
static double get_runtime()
{
    struct tms stop;
    times(&stop);
    return double(stop.tms_utime-start_time.tms_utime+stop.tms_stime-start_time.tms_stime)/sysconf(_SC_CLK_TCK);
}
static void start_timing()
{
    times(&start_time);
}

class Satlike
{
    private:
    vector<vector<int>> raw_clauses;
    vector<uint64_t> raw_weights;
    vector<int> labels;

    vector<vector<int>> orig_inst;
    vector<uint64_t> orig_weights;

    vector<int> hard_clauses;
    vector<int> soft_clauses;

    vector<tuple<long long, long long, long long>> actual_cost_analysis;

    vector<vector<int>> construct_hs();
    long long greedy_hs();
    void solve_hitting_set(vector<vector<int>> hs);
    bool sol_is_locally_minimal();


    unsigned long long flip_c;
    unsigned long long flip_goodvars;
    unsigned long long flip_no_goodvars;

    long long median_weight;

    unsigned int seed;

    long long get_cost();
    long long get_cost_by_reconstruction();
    /***********non-algorithmic information ****************/
    string filename;

    int problem_weighted;
    int partial; //1 if the instance has hard clauses, and 0 otherwise.

    int max_clause_length;
    int min_clause_length;

    //size of the instance
    int num_vars; //var index from 1 to num_vars
    int num_labels;
    int num_clauses; //clause index from 0 to num_clauses-1
    int num_groups;
    int num_hclauses;
    int num_sclauses;
    int num_lclauses;

    int previously_selected_group;

    //steps and time
    int tries;
    int max_tries;
    unsigned int max_flips;
    unsigned int max_non_improve_flip;
    unsigned int step;
    unsigned int max_total_flips;

    int print_time;
    int print_time1;
    int print_time2;
    int print1;
    int print2;
    int cutoff_time;
    int cutoff_time1;
    int cutoff_time2;
    int prioup_time;
    double opt_time;

    /**********end non-algorithmic information*****************/
    /* literal arrays */
    lit** var_lit;          //var_lit[i][j] means the j'th literal of var i.
    int*  var_lit_count;    //amount of literals of each var
    lit** clause_lit;       //clause_lit[i][j] means the j'th literal of clause i.
    int*  clause_lit_count; // amount of literals in each clause
    int*  clause_type;      // 0 == hard clause, 1 == soft clause, 2 == label clause
    int** var_group;
    int*  var_group_count;

    lit** var_label;
    int*  var_label_count;

    int*  clause_label; // defines clauses main label, used for grouping
    lit** clause_labels;
    int*  clause_label_count;



    /* Information about the variables. */
    long long* score;
    long long* time_stamp;
    long long* label_cost;
    int* configuration;

    int**   var_neighbor;
    int*    var_neighbor_count;
    int*    neighbor_flag;
    int*    temp_neighbor;

    /* Information about the clauses */
    long long  top_clause_weight;
    long long  min_soft_weight;
    long long  max_soft_weight;
    long long* org_clause_weight;
    long long  total_label_weight;
    long long* clause_weight;
    int* sat_count;
    int* sat_var;
    int* clause_group;

    /* information about the groups */
    int** group_vars;
    int** GM;  // group make
    int** GS;  // group score
    int*  GUC; // group unsat count
    int*  TSC; // temp group score
    int*  group_type; // 0 == hard grup, 1 == soft group, 2 == label group
    int*  group_size; // number of variables in group
    int*  best_soft_group;
    long long*  group_weight;
    long long*  org_group_weight;

    //original unit clause stack
    lit* unit_clause;
    int  unit_clause_count;

    //unsat groups stack
    int* hardgroupunsat_stack;        //store the unsat clause number
    int* index_in_hardgroupunsat_stack;//which position is a clause in the unsat_stack
    int  hardgroupunsat_stack_fill_pointer;
    int* already_in_hardgroupunsat_stack;

    int* softgroupunsat_stack;        //store the unsat clause number
    int* index_in_softgroupunsat_stack;//which position is a clause in the unsat_stack
    int  softgroupunsat_stack_fill_pointer;
    int* already_in_softgroupunsat_stack;

    int* labelgroupunsat_stack;        //store the unsat clause number
    int* index_in_labelgroupunsat_stack;//which position is a clause in the unsat_stack
    int  labelgroupunsat_stack_fill_pointer;
    int* already_in_labelgroupunsat_stack;

    //good decreasing variables (dscore>0 and confchange=1)
    int* goodvar_stack;
    int  goodvar_stack_fill_pointer;
    int* already_in_goodvar_stack;


    //label group selected counts used in pick_var (tabooing)
    long long* group_selected_count;
    int* best_label_group;

    /* Information about solution */
    int* cur_soln;    //the current solution, with 1's for True variables, and 0's for False variables
    int* best_soln;
    int* local_opt_soln;
    int* label_unsat_count;
    int best_soln_feasible; //when find a feasible solution, this is marked as 1.
    int local_soln_feasible;
    int hard_unsat_nb;
    long long label_unsat_weight;
    long long opt_unsat_weight;
    long long local_opt_unsat_weight;
    long long actual_opt_unsat_weight;
    long long actual_local_opt_unsat_weight;

    //clause weighting
    int* large_weight_clauses;
    int  large_weight_clauses_count;
    int  large_clause_count_threshold;

    int* label_large_weight_clauses;
    int* already_in_label_large_weight_stack;
    int  label_large_weight_clauses_count;
    int  label_large_clause_count_threshold;

    //tem data structure used in algorithm
    int* temp_lit;

    //parameters used in algorithm
    float rwprob;
    float rdprob;
    float smooth_probability;
    int hd_count_threshold;
    int h_inc;
    int h_inc_small;
    int h_inc_large;
    int labelclause_weight_threshold;

    double theta;
    double phi;
    double noise; // technically not a parameter (dynamic, depends on theta and phi)

    double group_sat_greedy;

    bool use_sat_solver;
    bool dec_soft_weights;
    bool divide_weights;
    double percentage_of_weights_to_zero;
    long long weight_divisor;

    //preprocessor
    maxPreprocessor::PreprocessorInterface *maxpre;
    CaDiCaL::Solver *sat_solver;
    bool black_box_pp = false;

    //function used in algorithm
    int parse_hard_clauses(vector<vector<int>> &raw_clauses, vector<uint64_t> &raw_weights);
    void parse_soft_clauses(int c, vector<vector<int>> &raw_clauses, vector<uint64_t> &raw_weights);
    void build_neighbor_relation();
    void build_groups();
    void allocate_memory();
    void init_sat_solver();
    bool verify_sol();
    void increase_weights();
    void increase_group_weights();
    void smooth_weights();
    void update_clause_weights();
    void unsat(const int clause);
    void sat(const int clause);
    void unsat_group(const int group);
    void sat_group(const int group);
    void init(vector<int>& init_solution);
    void flip(const int flipvar);
    void flip_var(const int flipvar);
    void update_group_makes(const int group);
    void update_goodvarstack(const int flipvar);
    void update_goodvarstack1(const int flipvar);
    void update_goodvarstack2(const int flipvar);
    int satisfy_group_without_label(const int group);
    int pick_var();
    void settings();
    void relabel_for_blackbox_pp();
    void add_labels();

    vector<int> labels_flipped_by_greedy_hs;
    int* sat_label;
    int* clause_label_sat_count;
    int* label_criticality_count;
    PriorityQueue<long long> non_critical_labels;
    void label_on(const int v);
    void label_off(const int v);

	void check_non_critical_vars();
	void print_clauses_of(int v);

    public:
    Satlike();
    void parse_params(int argc, char* argv[]);
    void build_instance();
    //void build_instance(char *filename);
    void local_search(vector<int>& init_solution);
    void local_search_with_decimation(vector<int>& init_solution, char* inputfile);
    void simple_print();
    void print_best_solution();
    void print_omit_assignment();
    void free_memory();
};
