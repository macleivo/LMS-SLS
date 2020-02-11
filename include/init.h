#pragma once

#include "basis_pms.h"

Satlike::Satlike()
{
    problem_weighted=1;
    partial=1; //1 if the instance has hard clauses, and 0 otherwise.

    flip_c = 0;
    flip_goodvars = 0;
    flip_no_goodvars = 0;

    black_box_pp = false;

    seed                          = 0;
    h_inc                         = 300;
    h_inc_small                   = 3;
    h_inc_large                   = 300;
    use_sat_solver                = false;
    dec_soft_weights              = false;
    divide_weights                = false;
    percentage_of_weights_to_zero = 0.1;
    rdprob=0.01;
    hd_count_threshold=15;
    theta = 1.0/6;
    phi = 0.2;
    group_sat_greedy = 0.8;

    max_tries = 100000000;
    max_flips = 200000000;
    max_non_improve_flip = 10000000;
    max_flips = max_non_improve_flip;
    max_total_flips = -1;

    max_clause_length=0;
    min_clause_length=100000000;

    //size of the instance
    num_vars=0; //var index from 1 to num_vars
    num_clauses=0; //clause index from 0 to num_clauses-1
    num_hclauses=0;
    num_lclauses=0;

    print_time=240;
    cutoff_time=301;

    print1=0;
    print2=0;
    print_time1=50;
    print_time2=260;
    cutoff_time1=60;
    cutoff_time2=300;
}


void Satlike::settings()
{
    //steps
    tries=0;
    step=1;

    large_clause_count_threshold=0;
    label_large_clause_count_threshold=0;

    /*
    rwprob=0.1;
    smooth_probability=0.01;
    */

    if((total_label_weight/num_labels)>10000)
    {
        h_inc=h_inc_large;
        labelclause_weight_threshold=500;
    }
    else
    {
        h_inc=h_inc_small;
        labelclause_weight_threshold=0;
    }
    /*
    //h_inc = 1 + (max_soft_weight - min_soft_weight) / (max_flips / 100);

    if (num_vars>2000)
    {
        rdprob=0.01;
        hd_count_threshold=15;
        rwprob=0.1;
        smooth_probability=0.0000001;
    }

    if(num_vars>321000 && num_vars<322000 && num_clauses>608900 && num_clauses<610000 && top_clause_weight>6730 && top_clause_weight<6750 && max_clause_length==23)
    {
        max_non_improve_flip = 1000000;
        max_flips = max_non_improve_flip;
    }
    */
    cout << "c hinc == " << h_inc << endl;
    cout << "c rdprob == " << rdprob << endl;
}


void Satlike::init(vector<int>& init_solution)
{
    int v,c,g;
    int i,j;
    hard_unsat_nb=0;
    label_unsat_weight=0;
    local_soln_feasible=0;
    local_opt_unsat_weight=top_clause_weight+1;
    noise = 0;

    previously_selected_group = -1;

    if(best_soln_feasible==0)
    {
        for (c = 0; c<num_clauses; ++c)
            already_in_label_large_weight_stack[c]=0;

        for(g=0; g < num_groups; ++g)
            if(group_type[g] == 0) group_weight[g] = 1;
            else group_weight[g] = 0;
    }
    else
    {
        //Initialize clause information
        for (c = 0; c<num_clauses; ++c)
        {
            already_in_label_large_weight_stack[c]=0;

            if (org_clause_weight[c]==top_clause_weight)
                clause_weight[c] = 1;
            else
            {
                clause_weight[c] = org_clause_weight[c];
                if(clause_weight[c]>1 && already_in_label_large_weight_stack[c]==0)
                {
                    already_in_label_large_weight_stack[c]=1;
                    label_large_weight_clauses[label_large_weight_clauses_count++] = c;
                }
            }
        }

        for(g=0; g < num_groups; ++g)
        {
            if(group_type[g] == 0) group_weight[g] = 1;
            else group_weight[g] = label_cost[g - num_hclauses + 1] / weight_divisor;
        }
    }

    //init solution
    if(init_solution.size()==0)
        for(v=1; v <= num_vars; ++v) cur_soln[v] = 0;
    else
        for(v=1; v <= num_vars; ++v) cur_soln[v] = init_solution[v];

    for(v=1; v <= num_vars; ++v) time_stamp[v] = 0;
    for(v=1; v <= num_vars; ++v) configuration[v] = 1;

    //init stacks
    hardgroupunsat_stack_fill_pointer  = 0;
    softgroupunsat_stack_fill_pointer  = 0;
    labelgroupunsat_stack_fill_pointer = 0;

    large_weight_clauses_count       = 0;
    label_large_weight_clauses_count = 0;

    for(g=0; g < num_groups; ++g)
        group_selected_count[g] = 0;

    label_unsat_weight = 0;
    for(v=1; v <= num_labels; ++v)
        label_unsat_count[v] = 0;
    for(v=1; v <= num_labels; ++v)
        cur_soln[v] = labels[v-1] < 0 ? 0 : 1;

    non_critical_labels.clear();
    for(v=1; v <= num_labels; ++v)
        label_criticality_count[v] = 0;
    for(c=0; c<num_clauses; ++c)
        clause_label_sat_count[c] = 0;

    /* figure out sat_count, sat_var and init unsat_stack */
    for(c=0; c<num_clauses; ++c)
    {
        sat_count[c] = 0;
        for(j=0; j<clause_lit_count[c]; ++j)
        {
            if (cur_soln[clause_lit[c][j].var_num] == clause_lit[c][j].sense)
            {
                ++sat_count[c];
                sat_var[c] = clause_lit[c][j].var_num;
            }
        }
        if (sat_count[c] == 0)
            unsat(c);
    }
    for(c=0; c < num_clauses; ++c)
        sat_label[c] = 0;
    for(c=0; c < num_clauses; ++c)
        if(sat_count[c] == 0 && clause_type[c] == 1)
            if(++label_unsat_count[clause_label[c]] == 1)
                label_on(clause_label[c]);

    check_non_critical_vars();

    //figure out GUC values
    for(g=0; g < num_groups; ++g) GUC[g] = 0;
    for(c=0; c < num_clauses; ++c)
        if(sat_count[c] == 0)
            ++GUC[clause_group[c]];

    for(g=0; g < num_groups; ++g)
        if(GUC[g] > 0)
            unsat_group(g);

    //figure out GM values
    for(g=0; g < num_groups; ++g)
        for(i=0; i < group_size[g]; ++i)
            GM[g][i] = 0;

    int pos_in_group_vars = -1;
    for(v=1; v <= num_vars; ++v)
    {
        score[v] = 0;
        for(i=0; i < var_lit_count[v]; ++i)
        {
            c = var_lit[v][i].clause_num;
            g = clause_group[c];
            pos_in_group_vars = -1;

            for(j = group_size[g] - 1; j >= 1; j /= 2)
                while(pos_in_group_vars + j < group_size[g] && group_vars[g][pos_in_group_vars + j] < v)
                    pos_in_group_vars += j;
            ++pos_in_group_vars;

            if(sat_count[c] == 0)
                ++GM[g][pos_in_group_vars];
            else if (sat_count[c]==1 && var_lit[v][i].sense==cur_soln[v])
                --GM[g][pos_in_group_vars];
        }
    }

    //figure out GS values
    for(g=0; g < num_groups; ++g)
        for(i=0; i < group_size[g]; ++i)
            GS[g][i] = 0;

    for(g=0; g < num_groups; ++g)
        if(GUC[g] > 0)
        {
            for(i=0; i < group_size[g]; ++i)
                if(GM[g][i] == GUC[g])
                    GS[g][i] = 1;
        }
        else
        {
            for(i=0; i < group_size[g]; ++i)
                if(GM[g][i] < 0)
                    GS[g][i] = -1;
        }

    //figure out scores
    for(v=1; v <= num_vars; ++v)
        score[v] = 0;

    for(g=0; g < num_groups; ++g)
        for(i=0; i < group_size[g]; ++i)
            if(GS[g][i] == 1)
                score[group_vars[g][i]] += group_weight[g];
            else if(GS[g][i] == -1)
                score[group_vars[g][i]] -= group_weight[g];

    //init goodvars stack
    goodvar_stack_fill_pointer = 0;
    for (v=1; v<=num_vars; v++)
    {
        if(score[v]>0)
        {
            already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
            mypush(v,goodvar_stack);
        }
        else
            already_in_goodvar_stack[v] = -1;
    }
}
