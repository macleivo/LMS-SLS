#pragma once

#include "basis_pms.h"
#include "build.h"
#include "deci.h"
#include "flip.h"
#include "init.h"
#include "weights.h"
#include "PriorityQueue.h"
#include <sstream>


int Satlike::pick_var()
{
    int i,v;
    int best_var;
    //cout << goodvar_stack_fill_pointer << " " << hardgroupunsat_stack_fill_pointer << " " << softgroupunsat_stack_fill_pointer << " " << endl;

    if(goodvar_stack_fill_pointer>0 )
    {
        ++flip_goodvars;
        if( (rand()%MY_RAND_MAX_INT)*BASIC_SCALE< rdprob )
            return goodvar_stack[rand()%goodvar_stack_fill_pointer];

        if (goodvar_stack_fill_pointer < hd_count_threshold)
        {
            best_var = goodvar_stack[0];
            for (i=1; i<goodvar_stack_fill_pointer; ++i)
            {
                v = goodvar_stack[i];
                if (score[v]>score[best_var]) best_var=v;
                else if (score[v]==score[best_var])
                {
                    if(time_stamp[v]<time_stamp[best_var]) best_var=v;
                }
            }
            //assert(configuration[best_var] == 1);
            return best_var;
        }
        else
        {
            best_var = goodvar_stack[rand()%goodvar_stack_fill_pointer];
            for (i=1; i<hd_count_threshold; ++i)
            {
                v = goodvar_stack[rand()%goodvar_stack_fill_pointer];
                if (score[v]>score[best_var]) best_var=v;
                else if (score[v]==score[best_var])
                {
                    if(time_stamp[v]<time_stamp[best_var]) best_var=v;
                }
            }
            return best_var;
        }
    }
    ++flip_no_goodvars;

    update_clause_weights();

    int sel_g;
    lit* p;

    //assert(hardgroupunsat_stack_fill_pointer > 0 || softgroupunsat_stack_fill_pointer > 0);
    if(hardgroupunsat_stack_fill_pointer > 0)
        sel_g = hardgroupunsat_stack[rand() % hardgroupunsat_stack_fill_pointer];
    else if(softgroupunsat_stack_fill_pointer > 0)
    {
        if( (rand()%MY_RAND_MAX_INT)*BASIC_SCALE< 1-noise)
        {
            long long best_selected_num;
            long long best_selected_weight;
            int best_soft_group_count;
            int g;
            best_soft_group[0]=softgroupunsat_stack[0];
            best_selected_weight=group_weight[softgroupunsat_stack[0]];
            best_selected_num=group_selected_count[softgroupunsat_stack[0]];
            best_soft_group_count=1;

            for(int j=1;j<softgroupunsat_stack_fill_pointer;++j)
            {
                g=softgroupunsat_stack[j];
                if(group_weight[g] > best_selected_weight)
                {
                    best_soft_group[0]=g;
                    best_selected_weight=group_weight[g];
                    best_soft_group_count=1;
                    best_selected_num=group_selected_count[g];
                }
                else if(group_weight[g]==best_selected_weight)
                {
                    best_soft_group[best_soft_group_count]=g;
                    best_soft_group_count++;
                }
            }
            sel_g=best_soft_group[rand()%best_soft_group_count];
        }
        else
        {
            long long best_selected_num;
            int best_soft_group_count;
            int g;
            best_soft_group[0]=softgroupunsat_stack[0];
            best_selected_num=group_selected_count[softgroupunsat_stack[0]];
            best_soft_group_count=1;

            for(int j=1;j<softgroupunsat_stack_fill_pointer;++j)
            {
                g=softgroupunsat_stack[j];
                if(group_selected_count[g]<best_selected_num)
                {
                    best_soft_group[0]=g;
                    best_selected_num=group_selected_count[g];
                    best_soft_group_count=1;
                }
                else if(group_selected_count[g]==best_selected_num)
                {
                    best_soft_group[best_soft_group_count]=g;
                    best_soft_group_count++;
                }
            }
            sel_g = best_soft_group[0];
            for(int j=1; j < best_soft_group_count; ++j)
                if(group_weight[sel_g] < group_weight[best_soft_group[j]])
                    sel_g = best_soft_group[j];
        }
        group_selected_count[sel_g]++;
    }
    return satisfy_group_without_label(sel_g);
}


int Satlike::satisfy_group_without_label(const int group)
{
    int i, j, n, best_i;

    n = group_size[group];
    if(n == 0)
        return rand() % (num_vars - num_labels) + num_labels + 1;
    j = 0;

    vector<int> indices; // a random permuation of the group variable indices
    for(i=0; i < n; ++i) indices.push_back(i);
    for(i=0; i < n; ++i) swap(indices[n-i-1], indices[rand() % (n-i)]);

    if(group_type[group] == 0)
    {
        best_i = rand() % n;
        for(int k : indices)
            if(score[group_vars[group][best_i]] < score[group_vars[group][k]])
                best_i = k;
        return group_vars[group][best_i];
    }

    while(GUC[group] > 0 && ++j < 1000)
    {
        best_i = indices[0];

        if( (rand()%MY_RAND_MAX_INT)*BASIC_SCALE < 1-group_sat_greedy)
            best_i = rand() % n;
        else
            for(int k : indices)
                if(GM[group][best_i] < GM[group][k])
                    best_i = k;

        if(GS[group][best_i] == 1)
            return group_vars[group][best_i];

        flip_var(group_vars[group][best_i]);
    }
    return group_vars[group][rand() % n];
}


void Satlike::local_search_with_decimation(vector<int>& init_solution, char* inputfile)
{
    settings();

    Decimation deci(var_lit,var_lit_count,clause_lit,org_clause_weight,top_clause_weight);
    deci.make_space(num_clauses,num_vars);

    for(int i=1;i<=num_vars;++i)
    {
        local_opt_soln[i]=rand()%2;
    }

    for(tries=1;tries<max_tries;++tries)
    {
        deci.init(local_opt_soln,best_soln,unit_clause,unit_clause_count,clause_lit_count);
        deci.unit_prosess();

        init_solution.resize(1+num_vars);
        if(use_sat_solver && best_soln_feasible == 0)
        {
            cout << "c using a sat solver to find an initial solution..." << endl;
            int res = sat_solver->solve();
            if(res == 20)
            {
                cout << "c hard clauses are unsatisfiable" << endl;
                return;
            }
            for(int i=1;i<=num_vars;++i)
                init_solution[i]=sat_solver->val(i) > 0 ? 1 : 0;
        }
        else
            for(int i=1;i<=num_vars;++i)
                init_solution[i]=deci.fix[i];

        init(init_solution);

        int d = 1;
        for(step=1; step<max_flips; ++step)
        {
            if(max_total_flips <= flip_c)
            {
                print_best_solution();
                return;
            }
            long long act_cost = label_unsat_weight;
            if(hard_unsat_nb == 0)
            {
                act_cost = greedy_hs();
                /*
                long long recons_cost = get_cost_by_reconstruction();

                actual_cost_analysis.push_back(make_tuple(label_unsat_weight, act_cost, recons_cost));
                for(int label=1; label <= num_labels; ++label)
                {
                    cur_soln[label] = labels[label-1] < 0 ? 0 : 1;
                    if(label_unsat_count[label] > 0)
                        cur_soln[label] = 1 - cur_soln[label];
                }
                */
            }
            //act_cost = label_unsat_weight;

            if (hard_unsat_nb==0 && (act_cost<opt_unsat_weight || best_soln_feasible==0) )
            {
                if(best_soln_feasible==0)
                {
                    best_soln_feasible=1;
                    opt_unsat_weight = act_cost;
                    cout <<"o "<<opt_unsat_weight<<endl;
                    for(int v=1; v<=num_vars; ++v) best_soln[v] = cur_soln[v];
                    //assert(verify_sol() == 1);
                    if(num_labels == num_vars)
                    {
                        cout << "c all the variables are labels" << endl;
                        return;
                    }
                    break;
                }
                if(label_unsat_weight<top_clause_weight)
                {
                    opt_unsat_weight = act_cost;
                    cout<<"o "<<opt_unsat_weight<<endl;

                    for(int v=1; v<=num_vars; ++v) best_soln[v] = cur_soln[v];
                    //assert(verify_sol() == 1);

                    if(opt_unsat_weight==0)
                    {
                        print_best_solution();
                        return;
                    }
                }
            }

            if(hard_unsat_nb==0 && (label_unsat_weight<local_opt_unsat_weight || local_soln_feasible==0))
            {
                if(label_unsat_weight<top_clause_weight)
                {
                    local_soln_feasible=1;
                    local_opt_unsat_weight=act_cost;
                    max_flips=step+max_non_improve_flip;
                    for(int v=1;v<=num_vars;++v) local_opt_soln[v]=cur_soln[v];
                    noise = noise - noise*2*phi;
                    d = step;
                }
            }

            if(hard_unsat_nb == 0)
                for(int label : labels_flipped_by_greedy_hs)
                    label_on(label);

            if(step - d > num_clauses * theta)
            {
                noise = noise + (1-noise)*phi;
                d = step;
            }


            if (step%1000==0)
            {
                double elapse_time=get_runtime();


                if(print1==0 && elapse_time>print_time1 && elapse_time<60)
                    print1=1;

                if(elapse_time > 60) print1=0;

                if(print2==0 && elapse_time>print_time2)
                    print2=1;

                if(elapse_time>=cutoff_time) {deci.free_memory();return;}
            }

            int flipvar = pick_var();
            flip_var(flipvar);
            time_stamp[flipvar] = step;
        }
    }
}

long long Satlike::greedy_hs()
{
    labels_flipped_by_greedy_hs.clear();
    while(!non_critical_labels.empty())
    {
        int label = non_critical_labels.top();
        label_off(label);
        labels_flipped_by_greedy_hs.push_back(label);
    }
    return label_unsat_weight;
}


vector<vector<int>> Satlike::construct_hs()
{
    vector<vector<int>> hs;
    for(int c : soft_clauses)
    {
        const vector<int> &clause = raw_clauses[c];
        vector<int> labels;
        bool is_sat = false;
        for(int i=0; i < clause.size(); ++i)
        {
            int lit = clause[i];
            int v = abs(lit);
            if(v <= num_labels)
            {
                labels.push_back(v);
                continue;
            }
            if(lit < 0 && cur_soln[v] == 0) is_sat = true;
            if(lit > 0 && cur_soln[v] == 1) is_sat = true;
        }
        if(is_sat) continue;
        hs.push_back(labels);
    }
    int units = 0;
    for(const auto &v : hs)
        if(v.size() == 1)
            units++;
    return hs;
}


/*
long long Satlike::greedy_hs()
{
    for(int label=1; label <= num_labels; ++label)
        cur_soln[label] = labels[label-1] < 0 ? 0 : 1;

    long long final_cost = 0;
    vector<vector<int>> hs = construct_hs();
    PriorityQueue<long long> pq(num_labels);

    vector<vector<int>> hs_occ(1+num_labels);
    vector<int>         hs_sat_count(hs.size());

    for(int i=0; i < hs.size(); ++i)
        for(int label : hs[i])
            hs_occ[abs(label)].push_back(i);

    for(int label=1; label <= num_labels; ++label)
        if(label_unsat_count[label] > 0)
        {
            pq.push(label_cost[label], label);
            for(int i : hs_occ[label])
                ++hs_sat_count[i];
        }

    vector<int> used_labels;
    while(!pq.empty())
    {
        int most_expensive_label = pq.top();
        pq.pop();

        bool critical = false;
        for(int i : hs_occ[most_expensive_label])
            if(hs_sat_count[i] == 1)
            {
                critical = true;
                break;
            }
        if(critical)
            used_labels.push_back(most_expensive_label);
        else
            for(int i : hs_occ[most_expensive_label])
                --hs_sat_count[i];
    }

    for(int label : used_labels) final_cost += label_cost[label];
    for(int label : used_labels) cur_soln[label] = labels[label-1] < 0 ? 1 : 0;
    //assert(sol_is_locally_minimal());

    return final_cost;
}
*/


/*
long long Satlike::greedy_hs()
{
    for(int label=1; label <= num_labels; ++label)
        cur_soln[label] = labels[label-1] < 0 ? 0 : 1;

    long long final_cost = 0;
    vector<vector<int>> hs = construct_hs();
    PriorityQueue<long long> pq(num_labels);

    vector<int>         unsat_occ(1+num_labels);
    vector<vector<int>> hs_occ(1+num_labels);
    vector<int>         hs_sat_count(hs.size());

    for(auto &v : hs)
        for(int label : v)
            ++unsat_occ[abs(label)];

    for(int i=0; i < hs.size(); ++i)
        for(int label : hs[i])
            hs_occ[abs(label)].push_back(i);

    for(int label=1; label <= num_labels; ++label)
        if(unsat_occ[label] > 0)
            pq.push(1 + label_cost[label] / unsat_occ[label], label);

    vector<int> used_labels;
    while(!pq.empty() && pq.top_priority() > 0)
    {
        int best_label = pq.top();

        for(int i : hs_occ[best_label])
        {
            if(hs_sat_count[i] > 0) continue;

            for(int lit : hs[i])
                if(--unsat_occ[abs(lit)] > 0)
                    pq.update_priority(1 + label_cost[abs(lit)] / unsat_occ[abs(lit)], abs(lit));
                else if(pq.contains(abs(lit)))
                    pq.update_priority(0, abs(lit));
        }

        for(int i : hs_occ[best_label])
            ++hs_sat_count[i];

        used_labels.push_back(best_label);
    }
    for(int v=0, i=unsat_occ[v]; v < unsat_occ.size(); i=unsat_occ[++v])
    {
        if(i != 0)
        {
            for(auto &s : hs)
            {
                for(int j : s)
                    cout << j << " ";
                cout << endl;
            }
            cout << "c " << v << " " << i << endl;
        }
        assert(i == 0);
    }

    pq.clear();
    for(int label : used_labels)
        pq.push(label_cost[label], label);

    used_labels.clear();
    while(!pq.empty())
    {
        int most_expensive_label = pq.top();
        pq.pop();

        bool critical = false;
        for(int i : hs_occ[most_expensive_label])
            if(hs_sat_count[i] == 1)
            {
                critical = true;
                break;
            }
        if(critical)
            used_labels.push_back(most_expensive_label);
        else
            for(int i : hs_occ[most_expensive_label])
                --hs_sat_count[i];
    }

    for(int label : used_labels) final_cost += label_cost[label];
    for(int label : used_labels) cur_soln[label] = labels[label-1] < 0 ? 1 : 0;
    assert(sol_is_locally_minimal());

    return final_cost;
}
*/


bool Satlike::sol_is_locally_minimal()
{
    vector<int> unique_save(1+num_labels);
    for(int rc : soft_clauses)
    {
        vector<int> saving_labels;
        for(int lit : raw_clauses[rc])
        {
            int v = abs(lit);
            int sense = lit < 0 ? 0 : 1;
            if(cur_soln[v] == sense)
            {
                if(v <= num_labels) saving_labels.push_back(v);
                else
                {
                    saving_labels.clear();
                    break;
                }
            }
            if(saving_labels.size() > 1)
                break;
        }
        if(saving_labels.size() == 1)
            ++unique_save[saving_labels[0]];
    }
    for(int label=1; label <= num_labels; ++label)
        if(unique_save[label] == 0 && cur_soln[label] == (labels[label-1] < 0 ? 1 : 0))
            return false;
    return true;
}


long long Satlike::get_cost_by_reconstruction()
{
    //vector<vector<int>> hs = construct_hs();
    //solve_hitting_set(hs);

    int v;
    vector<int> true_literals;
    for(v=1; v <= num_vars; ++v)
        if(cur_soln[v] == 0)
            true_literals.push_back(-v);
        else
            true_literals.push_back(v);
    vector<int> true_lits = maxpre->reconstruct(true_literals);
    vector<int> assignment(1 + true_lits.size());
    for(int i : true_lits)
        if(i < 0)
            assignment.at(-i) = 0;
        else
            assignment.at(i) = 1;

    bool sol_is_valid = 1;
    int i=0;
    long long unsat_w = 0;
    for(auto &c : orig_inst)
    {
        long long w = orig_weights[i++];
        bool flag = false;
        for(int lit : c)
        {
            int v = abs(lit);
            int sense = lit < 0 ? 0 : 1;
            if(assignment[v] == sense)
            {
                flag = true;
                break;
            }
        }
        if(!flag)
        {
            if(w == top_clause_weight)
            {
                sol_is_valid = 0;
            }
            else
                unsat_w += w;
        }
    }
    return unsat_w;
}


long long Satlike::get_cost()
{
    return get_cost_by_reconstruction();
}


bool Satlike::verify_sol()
{
    int v;
    vector<int> true_literals;
    for(v=1; v <= num_vars; ++v)
        if(best_soln[v] == 0)
            true_literals.push_back(-v);
        else
            true_literals.push_back(v);
    vector<int> true_lits = maxpre->reconstruct(true_literals);
    vector<int> assignment(1 + true_lits.size());
    for(int i : true_lits)
        if(i < 0)
            assignment.at(-i) = 0;
        else
            assignment.at(i) = 1;

    bool sol_is_valid = 1;
    int i=0;
    long long unsat_w = 0;
    for(auto &c : orig_inst)
    {
        long long w = orig_weights[i++];
        bool flag = false;
        for(int lit : c)
        {
            int v = abs(lit);
            int sense = lit < 0 ? 0 : 1;
            if(assignment[v] == sense)
            {
                flag = true;
                break;
            }
        }
        if(!flag)
        {
            if(w == top_clause_weight)
            {
                cout << "c hard clause " << i << " is unsatisfied!" << endl;
                sol_is_valid = 0;
            }
            else
                unsat_w += w;
        }
    }
    if(unsat_w != opt_unsat_weight)
    {
        cout << "c opt w is " << opt_unsat_weight << " but it should be " << unsat_w << endl;
        sol_is_valid = 0;
    }
    return sol_is_valid;
}


void Satlike::print_best_solution()
{
    if (best_soln_feasible==0) return;
    for(int i=1; i <= num_vars - num_labels; ++i)
        best_soln[i] = best_soln[i+num_labels];
    num_vars -= num_labels;


    /*
    sort(actual_cost_analysis.rbegin(), actual_cost_analysis.rend());
    actual_cost_analysis.erase( unique( actual_cost_analysis.begin(), actual_cost_analysis.end() ), actual_cost_analysis.end() );
    cout << "c trying to find a pair of solutions with app_cost1 > app_cost2 but act_cost1 < act_cost2 out of " << actual_cost_analysis.size() << " found (possible duplicate) assignments" << endl;
    int n_wrong = 0;
    for(int i=0; i < actual_cost_analysis.size(); ++i)
    {
        auto p1 = actual_cost_analysis[i];
        long long app_cost1, hs_cost1, act_cost1;
        tie(app_cost1, hs_cost1, act_cost1) = p1;
        if(hs_cost1 != act_cost1)
            ++n_wrong;
        for(int j=i+1; j < actual_cost_analysis.size(); ++j)
        {
            auto p2 = actual_cost_analysis[j];
            long long app_cost2, hs_cost2, act_cost2;
            if(app_cost1 > app_cost2 && act_cost2 > act_cost1)
                cout << "c (" << app_cost1 << ", " << act_cost1 << ") vs. (" << app_cost2 << ", " << act_cost2 << ")" << endl;
            if(app_cost1 < app_cost2 && act_cost2 < act_cost1)
                cout << "c (" << app_cost2 << ", " << act_cost2 << ") vs. (" << app_cost1 << ", " << act_cost1 << ")" << endl;
        }
    }
    for(auto p : actual_cost_analysis)
    {
        long long app_cost, hs_cost, act_cost;
        tie(app_cost, hs_cost, act_cost) = p;
        cout << "c cost pair " << app_cost << " " << hs_cost << " " << act_cost << endl;
    }
    cout << "c n_wrong == " << n_wrong << endl;
    */

    cout << "v ";
    for(int i=1; i <= num_vars; ++i)
    {
        if(best_soln[i] == 0) cout << "-";
        cout << i << " ";
    }
    cout << endl;
    cout << "o " << opt_unsat_weight << "\n";
    cout << "s UNKNOWN\n";

    cout << "c total number of flips " << flip_c << endl;
    cout << "c " << flip_goodvars << endl;
    cout << "c " << flip_no_goodvars << endl;
    //assert(verify_sol() == 1);
}
