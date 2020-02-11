#pragma once

#include "basis_pms.h"


void Satlike::update_clause_weights()
{
    increase_group_weights();
}


void Satlike::increase_group_weights()
{
    int i, j, g, v;
    for(i=0; i < hardgroupunsat_stack_fill_pointer; ++i)
    {
        g = hardgroupunsat_stack[i];
        group_weight[g] += h_inc;

        for(j=0; j < group_size[g]; ++j)
        {
            v = group_vars[g][j];
            score[v] += h_inc;
            if(score[v] > 0 && already_in_goodvar_stack[v] == -1)
            {
                already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                mypush(v,goodvar_stack);
            }
        }
    }
    if(!dec_soft_weights)
        return;

    int last_goodvar, index;
    for(i=0; i < softgroupunsat_stack_fill_pointer; ++i)
    {
        g = softgroupunsat_stack[i];
        if(group_weight[g] <= 0)
            continue;

        int dec = h_inc * GUC[g];
        if(dec == 0)
            continue;
        if(dec >= group_weight[g])
            dec = group_weight[g];
        group_weight[g] -= dec;

        for(j=0; j < group_size[g]; ++j)
        {
            v = group_vars[g][j];
            score[v] -= dec;
            if(score[v] <= 0 && already_in_goodvar_stack[v] >= 0)
            {
                last_goodvar = mypop(goodvar_stack);
                index = already_in_goodvar_stack[v];
                goodvar_stack[index] = last_goodvar;
                already_in_goodvar_stack[last_goodvar] = index;
                already_in_goodvar_stack[v] = -1;
            }
        }
    }
}


void Satlike::smooth_weights()
{
    int i, clause, v;

    for(i=0; i<large_weight_clauses_count; i++)
    {
        clause = large_weight_clauses[i];
        if(sat_count[clause]>0)
        {
            clause_weight[clause]-=h_inc;

            if(clause_weight[clause]==1)
            {
                large_weight_clauses[i] = large_weight_clauses[--large_weight_clauses_count];
                i--;
            }
            if(sat_count[clause] == 1)
            {
                v = sat_var[clause];
                score[v]+=h_inc;
                if (score[v]>0 && already_in_goodvar_stack[v]==-1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v,goodvar_stack);
                }
            }
        }
    }

    for(i=0; i<label_large_weight_clauses_count; i++)
    {
        clause = label_large_weight_clauses[i];
        if(sat_count[clause]>0)
        {
            clause_weight[clause]--;
            if(clause_weight[clause]==1 && already_in_label_large_weight_stack[clause]==1)
            {
                already_in_label_large_weight_stack[clause]=0;
                label_large_weight_clauses[i] = label_large_weight_clauses[--label_large_weight_clauses_count];
                i--;
            }
            if(sat_count[clause] == 1)
            {
                v = sat_var[clause];
                score[v]++;
                if (score[v]>0 && already_in_goodvar_stack[v]==-1)
                {
                    already_in_goodvar_stack[v] = goodvar_stack_fill_pointer;
                    mypush(v,goodvar_stack);
                }
            }
        }
    }
}
