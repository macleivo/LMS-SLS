#pragma once

#include "basis_pms.h"

void Satlike::print_clauses_of(int v)
{
    cout << "---start of clauses of " << v << endl;
    for(int i=0; i < var_label_count[v]; ++i)
    {
        int c;
        if(v <= num_labels)
            c = var_label[v][i].clause_num;
        else
            c = var_lit[v][i].clause_num;
        cout << c << ": ";
        for(int j=0; j < clause_lit_count[c]; ++j)
        {
            int sign = clause_lit[c][j].sense == 0 ? -1 : 1;
            cout << sign*clause_lit[c][j].var_num << " " << cur_soln[clause_lit[c][j].var_num] << "; ";
        }
        if(clause_type[c] == 1)
            for(int j=0; j < clause_label_count[c]; ++j)
            {
                int sign = clause_labels[c][j].sense == 0 ? -1 : 1;
                cout << sign*clause_labels[c][j].var_num << " " << cur_soln[clause_labels[c][j].var_num] << "; ";
            }
        cout << endl;
    }
    cout << "---end of clauses of " << v << endl;
}


void Satlike::check_non_critical_vars()
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
        {
            ++unique_save[saving_labels[0]];
        }
    }
    //cout << "non saving labels: " << endl;
    for(int label=1; label <= num_labels; ++label)
        if(unique_save[label] == 0 && cur_soln[label] != (labels[label-1] < 0 ? 0 : 1))
        {
            //cout << label << " " << var_lit_count[label] << " " << labels[label-1] << " " << cur_soln[label] <<  "; ";
            for(int i=0; i < var_lit_count[label]; ++i)
            {
                //cout << "jyyyyyh" << endl;
                int c = var_lit[label][i].clause_num;
                if(clause_type[c] != 1) continue;
                //cout << "clause " << c << " -- ";
                for(int j=0; j < clause_lit_count[c]; ++j)
                {
                    int sign = clause_lit[c][j].sense == 0 ? -1 : 1;
                    //cout << sign*clause_lit[c][j].var_num << " " << cur_soln[clause_lit[c][j].var_num] << "; ";
                }
                for(int j=0; j < clause_label_count[c]; ++j)
                {
                    int sign = clause_labels[c][j].sense == 0 ? -1 : 1;
                    //cout << sign*clause_labels[c][j].var_num << " " << cur_soln[clause_labels[c][j].var_num] << "; ";
                }
            }
            //cout << endl;
        }
    //cout << endl;
    for(int label=1; label <= num_labels; ++label)
        if(unique_save[label] == 0 && cur_soln[label] != (labels[label-1] < 0 ? 0 : 1))
        {
            if(!non_critical_labels.contains(label))
            {
                cout << label << " should be contained: " << label_criticality_count[label] << endl;
                print_clauses_of(label);
            }
            assert(non_critical_labels.contains(label));
        }
        else
        {
            if(non_critical_labels.contains(label))
            {
                cout << label << " shouldnt be contained: " << label_criticality_count[label] << endl;
                print_clauses_of(label);
            }
            assert(!non_critical_labels.contains(label));
        }
}


void Satlike::update_group_makes(int group)
{
    int  i;
    int  gs       = group_size[group];
    int  group_uc = GUC[group];
    int* group_m  = GM[group];
    int* group_s  = GS[group];
    int* vars     = group_vars[group];
    long long w   = group_weight[group];

    for(i=0; i < gs; ++i) group_m[i] += TSC[vars[i]];
    for(i=0; i < gs; ++i) TSC[vars[i]] = 0;

    if(group_uc == 0)
    {
        for(i=0; i < gs; ++i)
            if(group_m[i] < 0)
            {
                if(group_s[i] == 0) score[vars[i]] -= w; // from neutral to breaking
                else if(group_s[i] == 1) score[vars[i]] -= 2*w; // from making to breaking
                group_s[i] = -1;
            }
            else
            {
                score[vars[i]] -= group_s[i] * w;
                group_s[i] = 0;
            }
    }
    else
    {
        for(i=0; i < gs; ++i)
            if(group_m[i] == group_uc)
            {
                if(group_s[i] == 0) score[vars[i]] += w; // from neutral to making
                else if(group_s[i] == -1) score[vars[i]] += 2*w; // from breaking to making
                group_s[i] = 1;
            }
            else
            {
                score[vars[i]] -= group_s[i] * w;
                group_s[i] = 0;
            }
    }
    //for(i=0; i < gs; ++i) configuration[vars[i]] = 1;
}


void Satlike::flip_var(const int flipvar)
{
    //cout << "c flipping " << flipvar << endl;
    assert(flipvar > num_labels);
    ++flip_c;
    int prev_group;
    int i, j, v, c, g;
    long long w;
    bool group_is_sat;
    lit* clause_c;

    cur_soln[flipvar] = 1 - cur_soln[flipvar];

    for(i=0; i < var_lit_count[flipvar]; ++i)
    {
        c = var_lit[flipvar][i].clause_num;
        g = clause_group[c];
        if(group_type[g] != 0) break;
        clause_c = clause_lit[c];

        w = group_weight[g];
        if(cur_soln[flipvar] == var_lit[flipvar][i].sense)
        {
            if(++sat_count[c] == 2) score[sat_var[c]] += w; // 2->1
            else if(sat_count[c] == 1) // 0 -> 1
            {
                sat_var[c] = flipvar;
                score[flipvar] -= w;
                for(lit* p=clause_c; (v=p->var_num)!=0; ++p)
                    score[v] -= w;
                sat(c);
                sat_group(g);
            }
        }
        else
        {
            if(--sat_count[c] == 1) // 2 -> 1
            {
                for(lit* p=clause_c; (v=p->var_num)!=0; ++p)
                    if(cur_soln[v] == p->sense)
                    {
                        sat_var[c] = v;
                        score[v] -= w;
                        break;
                    }
            }
            else if(sat_count[c] == 0) // 1 -> 0
            {
                score[flipvar] += w;
                for(lit* p=clause_c; (v=p->var_num)!=0; ++p)
                    score[v] += w;
                unsat(c);
                unsat_group(g);
            }
        }

    }
    if(i == var_lit_count[flipvar])
    {
        update_goodvarstack(flipvar);
        return;
    }

    vector<int> sat_v;
    vector<int> unsat_v;
    prev_group = clause_group[var_lit[flipvar][i].clause_num];
    group_is_sat = GUC[prev_group] == 0;

    for(; i < var_lit_count[flipvar]; ++i)
    {
        c = var_lit[flipvar][i].clause_num;
        g = clause_group[c];
        assert(group_type[g] != 0);
        clause_c = clause_lit[c];

        if(prev_group != g)
        {
            if(group_is_sat && GUC[prev_group] > 0) unsat_group(prev_group);
            else if(!group_is_sat && GUC[prev_group] == 0) sat_group(prev_group);
            update_group_makes(prev_group);

            group_is_sat = GUC[g] == 0;
        }
        prev_group = g;

        if(cur_soln[flipvar] == var_lit[flipvar][i].sense)
        {
            if(++sat_count[c] == 2) ++TSC[sat_var[c]]; // 2->1
            else if(sat_count[c] == 1) // 0 -> 1
            {
                sat_var[c] = flipvar;
                --TSC[flipvar];
                --GUC[g];

                for(lit* p=clause_c; (v=p->var_num)!=0; ++p)
                    --TSC[v];
                sat_v.push_back(c);
                sat(c);
            }
        }
        else
        {
            if(--sat_count[c] == 1) // 2 -> 1
            {
                for(lit* p=clause_c; (v=p->var_num)!=0; ++p)
                    if(cur_soln[v] == p->sense)
                    {
                        sat_var[c] = v;
                        --TSC[v];
                        break;
                    }
            }
            else if(sat_count[c] == 0) // 1 -> 0
            {
                ++TSC[flipvar];
                ++GUC[g];
                for(lit* p=clause_c; (v=p->var_num)!=0; ++p)
                    ++TSC[v];
                unsat_v.push_back(c);
                unsat(c);
            }
        }
    }
    if(group_is_sat && GUC[prev_group] > 0) unsat_group(prev_group);
    else if(!group_is_sat && GUC[prev_group] == 0) sat_group(prev_group);
    update_group_makes(prev_group);

    for(const int clause : unsat_v)
    {
        assert(sat_count[clause] == 0);
        int v = clause_label[clause];
        if(++label_unsat_count[v] == 1)
            label_on(v);
    }
    for(const int clause : sat_v)
    {
        int v = clause_label[clause];
        if(--label_unsat_count[v] == 0)
            label_off(v);
    }

    //configuration[flipvar] = 0;
    update_goodvarstack(flipvar);
	//check_non_critical_vars();
}


inline void Satlike::unsat(const int clause)
{
    if(clause_type[clause] == 0)
    {
        ++hard_unsat_nb;
    }
    else if(clause_type[clause] == 1)
    {
        assert(sat_count[clause] == 0);
        int v = clause_label[clause];

        if(clause_label_sat_count[clause] == 1)
        {
            int var = sat_label[clause];
            assert(var > 0);
            if(++label_criticality_count[var] == 1 && non_critical_labels.contains(var))
                non_critical_labels.pop(var);
        }
            /*
            for(int i=0; i < clause_label_count[clause]; ++i)
            {
                int sense = clause_labels[clause][i].sense;
                int var   = clause_labels[clause][i].var_num;
                if(sense == cur_soln[var])
                {
                    if(++label_criticality_count[var] == 1 && non_critical_labels.contains(var))
                        non_critical_labels.pop(var);
                    break;
                }
            }
            */
    }
}

inline void Satlike::label_on(const int v)
{
    for(int i=0; i < var_label_count[v]; ++i)
    {
        int c = var_label[v][i].clause_num;
        ++clause_label_sat_count[c];
        if(clause_label_sat_count[c] == 1) sat_label[c] = v;
        if(sat_count[c] == 0 && clause_label_sat_count[c] == 1) // v becomes the only thing to save c
        {
            bool v_becomes_critical = ++label_criticality_count[v] == 1;
            if(v_becomes_critical && non_critical_labels.contains(v))
                non_critical_labels.pop(v);
        }
        else if(sat_count[c] == 0 && clause_label_sat_count[c] == 2)
        {
            int var = sat_label[c];
            assert(var > 0 && "label_on");
            bool var_becomes_non_critical = --label_criticality_count[var] == 0;
            if(var_becomes_non_critical)
                non_critical_labels.push(label_cost[var], var);
            /*
            for(int j=0; j < clause_label_count[c]; ++j)
            {
                int sense = clause_labels[c][j].sense;
                int var = clause_labels[c][j].var_num;
                if(sense == cur_soln[var]) // var is no longer critical in c
                {
                    bool var_becomes_non_critical = --label_criticality_count[var] == 0;
                    if(var_becomes_non_critical)
                        non_critical_labels.push(label_cost[var], var);
                    break;
                }
            }
            */
        }
    }
    if(label_criticality_count[v] == 0)
        non_critical_labels.push(label_cost[v], v);

    label_unsat_weight += label_cost[v];
    cur_soln[v] = 1 - cur_soln[v];
}

inline void Satlike::label_off(const int v)
{
    label_unsat_weight -= label_cost[v];
    cur_soln[v] = 1 - cur_soln[v];

    for(int i=0; i < var_label_count[v]; ++i)
    {
        int c = var_label[v][i].clause_num;
        --clause_label_sat_count[c];

        if(clause_label_sat_count[c] == 1)
        {
            // find the sat_label
            for(int j=0; j < clause_label_count[c]; ++j)
            {
                int sense = clause_labels[c][j].sense;
                int var = clause_labels[c][j].var_num;
                if(sense == cur_soln[var]) // var is no longer critical in c
                {
                    sat_label[c] = var;
                    break;
                }
            }
            // sat_label[c] is now critical in c
            if(sat_count[c] == 0)
            {
                int var = sat_label[c];
                bool var_becomes_critical = ++label_criticality_count[var] == 1;
                if(var_becomes_critical && non_critical_labels.contains(var))
                    non_critical_labels.pop(var);
            }
        }
    }
    label_criticality_count[v] = 0;
    if(non_critical_labels.contains(v))
        non_critical_labels.pop(v);
}



inline void Satlike::sat(const int clause)
{
    if(clause_type[clause] == 0)
        --hard_unsat_nb;
    else if(clause_type[clause] == 1)
    {
        int v = clause_label[clause];
        assert(sat_count[clause] == 1);

        if(clause_label_sat_count[clause] == 1) // saving label is no longer critical
        {
            int var = sat_label[clause];
            if(--label_criticality_count[var] == 0)
                non_critical_labels.push(label_cost[var], var);

            /*
            for(int i=0; i < clause_label_count[clause]; ++i)
            {
                int sense = clause_labels[clause][i].sense;
                int var = clause_labels[clause][i].var_num;
                if(cur_soln[var] == sense)
                {
                    if(--label_criticality_count[var] == 0)
                        non_critical_labels.push(label_cost[var], var);
                    break;
                }
            }
            */
        }
    }
}


inline void Satlike::unsat_group(const int group)
{
    if(group_type[group] == 0)
    {
        index_in_hardgroupunsat_stack[group] = hardgroupunsat_stack_fill_pointer;
        mypush(group, hardgroupunsat_stack);
    }
    else if(group_type[group] == 1)
    {
        if(group_size[group] > 0)
        {
            index_in_softgroupunsat_stack[group] = softgroupunsat_stack_fill_pointer;
            mypush(group, softgroupunsat_stack);
        }
    }
}


inline void Satlike::sat_group(const int group)
{
    int index, last_unsat_group;
    if(group_type[group] == 0)
    {
        last_unsat_group = mypop(hardgroupunsat_stack);
        index = index_in_hardgroupunsat_stack[group];
        hardgroupunsat_stack[index] = last_unsat_group;
        index_in_hardgroupunsat_stack[last_unsat_group] = index;
    }
    else if(group_type[group] == 1)
    {
        if(group_size[group] > 0)
        {
            last_unsat_group = mypop(softgroupunsat_stack);
            index = index_in_softgroupunsat_stack[group];
            softgroupunsat_stack[index] = last_unsat_group;
            index_in_softgroupunsat_stack[last_unsat_group] = index;
        }
    }
}


// flipvar is not in goodvarstack after this even if its score went positive
// after flipping it, since flipvar is not its own neighbour!! This might be
// a good thing though as we dont want to flip flipvar again immediately.
void Satlike::update_goodvarstack(const int flipvar)
{
    int i, j, c, g, v, index;
    int* gv;
    //remove the vars no longer goodvar in goodvar stack
    for(index=goodvar_stack_fill_pointer-1; index>=0; index--)
    {
        v = goodvar_stack[index];
        if(score[v]<=0 || configuration[v] == 0)
        {
            goodvar_stack[index] = mypop(goodvar_stack);
            already_in_goodvar_stack[v] = -1;
        }
    }

    for(i=0; i < var_neighbor_count[flipvar]; ++i)
    {
        v = var_neighbor[flipvar][i];
        if(already_in_goodvar_stack[v] == -1 && score[v] > 0 && configuration[v] == 1)
        {
            already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
            mypush(v,goodvar_stack);
        }
    }
}
