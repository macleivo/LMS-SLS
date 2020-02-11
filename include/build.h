#pragma once

#include "basis_pms.h"
#include <cassert>
#include <algorithm>


void Satlike::parse_params(int argc, char* argv[])
{
    if(argc == 2)
    {
        filename = argv[1];
        return;
    }
    vector<string> arguments;
    for(int i=1; i < argc; ++i)
        arguments.push_back(string(argv[i]));

    int n = arguments.size();
    for(int i=0; i < n; i++)
    {
        if(arguments[i] == "-inst"             ) filename                      = arguments[i+1];
        if(arguments[i] == "-seed"             ) seed                          = stoi(arguments[i+1]);
        if(arguments[i] == "-h_inc"            ) h_inc_small                   = stoi(arguments[i+1]);
        if(arguments[i] == "-h_inc"            ) h_inc_large                   = stoi(arguments[i+1]);
        if(arguments[i] == "-h_inc_small"      ) h_inc_small                   = stoi(arguments[i+1]);
        if(arguments[i] == "-h_inc_large"      ) h_inc_large                   = stoi(arguments[i+1]);
        if(arguments[i] == "-use_sat_solver"   ) use_sat_solver                = stoi(arguments[i+1]);
        if(arguments[i] == "-dec_sw"           ) dec_soft_weights              = stoi(arguments[i+1]);
        if(arguments[i] == "-div_w"            ) divide_weights                = stoi(arguments[i+1]);
        if(arguments[i] == "-pwz"              ) percentage_of_weights_to_zero = stod(arguments[i+1]);
        if(arguments[i] == "-theta"            ) theta                         = stod(arguments[i+1]);
        if(arguments[i] == "-phi"              ) phi                           = stod(arguments[i+1]);
        if(arguments[i] == "-rdprob"           ) rdprob                        = stod(arguments[i+1]);
        if(arguments[i] == "-group_sat_greedy" ) group_sat_greedy              = stod(arguments[i+1]);
        if(arguments[i] == "-flip_count"       ) max_total_flips               = stoul(arguments[i+1]);
    }
}


void Satlike::relabel_for_blackbox_pp()
{
    black_box_pp = true;

    // ei pitäis tarvii palauttaa raw_clauses yms. riittää shiftaa muuttujat takas
    // shift variables
    int variable_shift = int(labels.size());
    for(int rc=0; rc < int(raw_clauses.size()); ++rc)
        for(int i=0; i < raw_clauses[rc].size(); ++i)
            if(raw_clauses[rc][i] < 0) raw_clauses[rc][i] -= variable_shift;
            else if(raw_clauses[rc][i] > 0) raw_clauses[rc][i] += variable_shift;

    // add new labels
    //for(int i=1; i <= variable_shift; ++i) raw_clauses.push_back({-i});
    int new_label = 0;
    int num_orig_clauses = int(raw_clauses.size());
    for(int rc=0; rc < num_orig_clauses; ++rc)
    {
        if(raw_weights[rc] != top_clause_weight)
        {
            // add label to clause rc and create new clause for label
            ++new_label;
            raw_clauses[rc].push_back(new_label);
            raw_clauses.push_back({-new_label});

            // add the weight of the new label clause
            raw_weights.push_back(raw_weights[rc]);

            // make the old label clause a hard
            raw_weights[rc] = top_clause_weight;
        }
    }

    labels.clear();
    for(int i=1; i <= variable_shift; ++i)
        labels.push_back(-i);
}


void Satlike::add_labels()
{
    int num_labels = 0;
    for(int rc=0; rc < raw_clauses.size(); ++rc)
        if(raw_weights[rc] != top_clause_weight)
            ++num_labels;

    //shift variables
    for(int rc=0; rc < raw_clauses.size(); ++rc)
        for(int i=0; i < raw_clauses[rc].size(); ++i)
            if(raw_clauses[rc][i] < 0)
                raw_clauses[rc][i] -= num_labels;
            else if(raw_clauses[rc][i] > 0)
                raw_clauses[rc][i] += num_labels;

    int label = 0;
    int num_clauses = raw_clauses.size();
    for(int rc=0; rc < num_clauses; ++rc)
        if(raw_weights[rc] != top_clause_weight)
        {
            // add label to clause rc and create new clause for label
            ++label;
            raw_clauses[rc].push_back(label);
            raw_clauses.push_back({-label});

            raw_weights.push_back(raw_weights[rc]);
            raw_weights[rc] = top_clause_weight;
        }

    for(int label=1; label <= num_labels; ++label)
        labels.push_back(-label);
}


void Satlike::build_instance()
{
    if(seed > 0)
        srand(seed);

    flip_c = 0;
    istringstream iss;
    char    line[1024];
    string  line2;
    char    tempstr1[10];
    char    tempstr2[10];
    int     cur_lit;
    int     i,v,c,n;
    //int     temp_lit[MAX_VARS];

    ifstream infile(filename);
    if(infile.fail())
    {
        cout<<"c the input filename "<<filename<<" is invalid, please input the correct filename."<<endl;
        exit(-1);
    }

    /*** build problem data structures of the instance ***/

    getline(infile,line2);

    while(line2[0]!='p')
    {
        getline(infile,line2);
    }
    for(i=0;i<1024;i++)
    {
        line[i]=line2[i];
    }
    int read_items;

    read_items=sscanf(line, "%s %s %d %d %lld", tempstr1, tempstr2, &num_vars, &num_clauses, &top_clause_weight);

    if(read_items<5)
    {
        if(strcmp(tempstr2,"cnf")==0)
        {
            problem_weighted=0;
        }

        partial = 0;
        top_clause_weight=-1;
    }

    //Now, read the clauses, one at a time.
    int lit_redundent,clause_redundent;

    while(getline(infile, line2))
    {
        if(line2[0] == 'c') continue;
        else
        {
            iss.clear();
            iss.str(line2);
            iss.seekg(0, ios::beg);
        }

        raw_clauses.push_back({});

        uint64_t clause_w = 1;
        if(problem_weighted != 0)
            iss >> clause_w;
        raw_weights.push_back(clause_w);

        iss >> cur_lit;
        while(cur_lit != 0)
        {
            raw_clauses.back().push_back(cur_lit);
            iss >> cur_lit;
        }
    }
    infile.close();
    for(auto i : raw_clauses)
        orig_inst.push_back(i);
    orig_weights = raw_weights;

    // preprocess
    //maxpre = new maxPreprocessor::PreprocessorInterface(raw_clauses, raw_weights, top_clause_weight);

    string techniques = "[bu]#[buvsrg]";
    //techniques = "[u]#[uvsrg]";
    techniques = "";
    black_box_pp = false;
    add_labels();

    /*
    maxpre->setBVEsortMaxFirst(true);
    maxpre->setBVElocalGrowLimit(10);
    maxpre->setBVEglobalGrowLimit(1000);
    maxpre->preprocess(techniques, 0, 10);
    maxpre->getInstance(raw_clauses, raw_weights, labels);

    maxpre->printTechniqueLog(cout);
    maxpre->printTimeLog(cout);
    maxpre->printInfoLog(cout);
    */

    if(black_box_pp)
        relabel_for_blackbox_pp();

    set<int> temp_vars;
    for(auto &v : raw_clauses)
        for(int lit : v)
            temp_vars.insert(abs(lit));

    num_vars    = int(temp_vars.size());
    num_labels  = int(labels.size());
    num_clauses = int(raw_clauses.size());

    // end preprocess

    allocate_memory();

    for (c = 0; c < num_clauses; c++)
    {
        clause_lit_count[c] = 0;
        clause_lit[i]=NULL;
        clause_label_count[c] = 0;
        clause_labels[i]=NULL;
    }
    for (v=1; v<=num_vars; ++v)
    {
        var_lit_count[v] = 0;
        var_lit[v]=NULL;

        var_label_count[v] = 0;
        var_label[v]=NULL;
    }


    min_soft_weight = top_clause_weight;
    max_soft_weight = 0;
    vector<int64_t> label_weights;
    for(int rc=0; rc < int(raw_clauses.size()); rc++)
    {
        if(int64_t(raw_weights[rc]) != top_clause_weight)
        {
            total_label_weight += int64_t(raw_weights[rc]);
            label_weights.push_back(int64_t(raw_weights[rc]));
            assert(raw_clauses[rc].size() == 1);
            label_cost[abs(raw_clauses[rc][0])] = int64_t(raw_weights[rc]);
            if(int64_t(raw_weights[rc]) < min_soft_weight)
                min_soft_weight = int64_t(raw_weights[rc]);
            if(int64_t(raw_weights[rc]) > max_soft_weight)
                max_soft_weight = int64_t(raw_weights[rc]);
            continue;
        }
        bool is_hard = true;
        for(int cur_lit : raw_clauses[rc])
            if(abs(cur_lit) <= num_labels)
                is_hard = false;
        if(is_hard) hard_clauses.push_back(rc);
        else soft_clauses.push_back(rc);
    }
    sort(label_weights.begin(), label_weights.end());
    median_weight = label_weights[label_weights.size() / 2];

    weight_divisor = label_weights[int(label_weights.size() * percentage_of_weights_to_zero)];
    if(!divide_weights)
        weight_divisor = 1;
    cout << "c weight_divisor == " << weight_divisor << endl;

    // assumes there are no tautologies or duplicate literals in clauses
    num_hclauses = int(hard_clauses.size());
    num_sclauses = int(soft_clauses.size());
    num_clauses  = num_hclauses + num_sclauses;
    unit_clause_count=0;

    c=0;
    for(int rc : hard_clauses)
    {
        clause_type[c] = 0;
        clause_group[c] = c;
        clause_lit_count[c] = int(raw_clauses[rc].size());
        org_clause_weight[c] = int64_t(raw_weights[rc]);
        clause_lit[c] = new lit[1+clause_lit_count[c]];

        for(i=0; i<clause_lit_count[c]; ++i)
        {
            clause_lit[c][i].clause_num = c;
            clause_lit[c][i].var_num = abs(raw_clauses[rc][i]);

            if (raw_clauses[rc][i] > 0) clause_lit[c][i].sense = 1;
            else clause_lit[c][i].sense = 0;

            var_lit_count[clause_lit[c][i].var_num]++;
        }

        clause_lit[c][i].var_num=0;
        clause_lit[c][i].clause_num = -1;

        if(clause_lit_count[c]==1) unit_clause[unit_clause_count++]=clause_lit[c][0];

        if(clause_lit_count[c]>max_clause_length) max_clause_length=clause_lit_count[c];
        if(clause_lit_count[c]<min_clause_length) min_clause_length=clause_lit_count[c];

        c++;
    }
    for(int rc : soft_clauses)
    {
        clause_type[c] = 1;
        vector<int> literals;
        vector<int> labels;
        for(int lit : raw_clauses[rc])
            if(abs(lit) > num_labels) literals.push_back(lit);
            else labels.push_back(lit);

        clause_label[c] = abs(labels[0]);
        for(int lit : labels)
        {
            int v = abs(lit);
            if(label_cost[v] < label_cost[clause_label[c]])
                clause_label[c] = abs(v);
        }
        clause_group[c] = num_hclauses + clause_label[c] - 1;
        clause_group[c] = c;

        clause_label_count[c] = int(labels.size());
        clause_labels[c]      = new lit[1+clause_label_count[c]];
        for(i=0; i < clause_label_count[c]; ++i)
        {
            clause_labels[c][i].clause_num = c;
            clause_labels[c][i].var_num = abs(labels[i]);

            if(labels[i] > 0) clause_labels[c][i].sense = 1;
            else clause_labels[c][i].sense = 0;

            var_label_count[clause_labels[c][i].var_num]++;
        }

        clause_lit_count[c] = int(literals.size());
        org_clause_weight[c] = int64_t(raw_weights[rc]);
        clause_lit[c] = new lit[1+clause_lit_count[c]];

        for(i=0; i<clause_lit_count[c]; ++i)
        {
            clause_lit[c][i].clause_num = c;
            clause_lit[c][i].var_num = abs(literals[i]);

            if(literals[i] > 0) clause_lit[c][i].sense = 1;
            else clause_lit[c][i].sense = 0;

            var_lit_count[clause_lit[c][i].var_num]++;
        }

        clause_lit[c][i].var_num=0;
        clause_lit[c][i].clause_num = -1;

        if(clause_lit_count[c]==1) unit_clause[unit_clause_count++]=clause_lit[c][0];

        if(clause_lit_count[c]>max_clause_length) max_clause_length=clause_lit_count[c];
        if(clause_lit_count[c]<min_clause_length) min_clause_length=clause_lit_count[c];

        c++;
    }

    //create var literal arrays
    for (v=1; v<=num_vars; ++v)
    {
        var_lit[v] = new lit[var_lit_count[v]+1];
        var_label[v] = new lit[var_label_count[v]+1];
        var_lit_count[v] = 0;    //reset to 0, for build up the array
        var_label_count[v] = 0;
    }
    //scan all clauses to build up var literal arrays
    for (c = 0; c < num_clauses; ++c)
    {
        for(i=0; i<clause_lit_count[c]; ++i)
        {
            v = clause_lit[c][i].var_num;
            var_lit[v][var_lit_count[v]] = clause_lit[c][i];
            ++var_lit_count[v];
        }
        for(i=0; i<clause_label_count[c]; ++i)
        {
            v = clause_labels[c][i].var_num;
            var_label[v][var_label_count[v]] = clause_labels[c][i];
            ++var_label_count[v];
        }
    }
    for (v=1; v<=num_vars; ++v)
        var_lit[v][var_lit_count[v]].clause_num=-1;

    for(v=1; v <= num_vars; ++v)
        TSC[v] = 0;

    build_groups();
    build_neighbor_relation();

    best_soln_feasible=0;
    opt_unsat_weight=total_label_weight+1;

    init_sat_solver();
    non_critical_labels.resize(num_labels);
}


void Satlike::init_sat_solver()
{
    sat_solver = new CaDiCaL::Solver();
    sat_solver->reserve(num_vars);
    for(int rc : hard_clauses)
    {
        for(int lit : raw_clauses[rc])
            sat_solver->add(lit);
        sat_solver->add(0);
    }
}


void Satlike::build_groups()
{
    cout << "c building groups..." << endl;
    int group = 0;
    int i, c, g, v, prev_v, group_vars_num, malloc_group_length;

    for(c=0; c < num_clauses; ++c)
        for(i=0; i < clause_lit_count[c]; ++i)
            clause_lit[c][i].group_num = clause_group[c];

    for(v=1; v <= num_vars; ++v)
        for(i=0; i < var_lit_count[v]; ++i)
            var_lit[v][i].group_num = clause_group[var_lit[v][i].clause_num];

    for(v=1; v <= num_vars; ++v)
        for(i=0; i < var_label_count[v]; ++i)
            var_label[v][i].group_num = clause_group[var_label[v][i].clause_num];

    for(v=1; v <= num_vars; ++v)
        sort(var_lit[v], var_lit[v]+var_lit_count[v], sort_lit_by_group);
    for(v=1; v <= num_vars; ++v)
        sort(var_label[v], var_label[v]+var_label_count[v], sort_lit_by_group);

    for(v=1; v <= num_vars; ++v)
    {
        vector<int> temp_var_groups;
        for(i=0; i < var_lit_count[v]; ++i)
            temp_var_groups.push_back(var_lit[v][i].group_num);
        sort(temp_var_groups.begin(), temp_var_groups.end());
        temp_var_groups.erase(unique(temp_var_groups.begin(), temp_var_groups.end()), temp_var_groups.end());

        int n = temp_var_groups.size();
        var_group[v] = new int [1+n];
        var_group_count[v] = n;
        for(i=0; i < n; ++i)
            var_group[v][i] = temp_var_groups[i];
    }

    num_groups = num_hclauses + num_labels;
    set<int> temp_groups;
    for(c=0; c < num_clauses; ++c)
        temp_groups.insert(clause_group[c]);
    for(int i : temp_groups)
        num_groups = num_groups < i ? i : num_groups;

    malloc_group_length = 10+num_groups;

    // allocate group vars
    group_vars       = new int* [malloc_group_length];
    GM               = new int* [malloc_group_length];
    GS               = new int* [malloc_group_length];
    GUC              = new int  [malloc_group_length];
    group_type       = new int  [malloc_group_length];
    group_size       = new int  [malloc_group_length];
    best_soft_group  = new int  [malloc_group_length];
    group_weight     = new long long [malloc_group_length];
    org_group_weight = new long long [malloc_group_length];

    hardgroupunsat_stack            = new int [malloc_group_length];
    index_in_hardgroupunsat_stack   = new int [malloc_group_length];
    already_in_hardgroupunsat_stack = new int [malloc_group_length];

    softgroupunsat_stack            = new int [malloc_group_length];
    index_in_softgroupunsat_stack   = new int [malloc_group_length];
    already_in_softgroupunsat_stack = new int [malloc_group_length];

    labelgroupunsat_stack            = new int [malloc_group_length];
    index_in_labelgroupunsat_stack   = new int [malloc_group_length];
    already_in_labelgroupunsat_stack = new int [malloc_group_length];

    best_label_group     = new int [malloc_group_length];
    group_selected_count = new long long [malloc_group_length];

    for(c=0; c < num_clauses; ++c)
        group_type[clause_group[c]] = clause_type[c];

    vector<vector<int>> temp_group_vars(malloc_group_length);
    for(c=0; c < num_clauses; ++c)
    {
        g = clause_group[c];
        if(group_weight[g] == 0)
            org_group_weight[g] = org_clause_weight[c];

        for(i=0; i < clause_lit_count[c]; ++i)
            temp_group_vars[clause_group[c]].push_back(clause_lit[c][i].var_num);
    }

    for(g=0; g < malloc_group_length; g++)
    {
        sort(temp_group_vars[g].begin(), temp_group_vars[g].end());
        temp_group_vars[g].erase(unique(temp_group_vars[g].begin(), temp_group_vars[g].end()), temp_group_vars[g].end());

        group_size[g]  = int(temp_group_vars[g].size());
        group_vars[g]  = new int [1+group_size[g]];
        GM[g]          = new int [1+group_size[g]];
        GS[g]          = new int [1+group_size[g]];

        for(i=0; i < group_size[g]; i++)
            group_vars[g][i] = temp_group_vars[g][i];
    }

    cout << "c built the groups" << endl;
}


void Satlike::build_neighbor_relation()
{
    cout << "c building neighbour relations" << endl;
    int i,j,count;
    int v,g,n;
    int temp_neighbor_count;
    int* gv;

    for(v=1; v<=num_vars; ++v)
    {
        neighbor_flag[v] = 1;
        temp_neighbor_count = 0;

        for(i=0; i < var_group_count[v]; ++i)
        {
            g = var_group[v][i];
            gv = group_vars[g];
            for(j=0; j < group_size[g]; ++j)
            {
                n = gv[j];
                if(neighbor_flag[n]!=1)
                {
                    neighbor_flag[n] = 1;
                    temp_neighbor[temp_neighbor_count++] = n;
                }
            }
        }

        neighbor_flag[v] = 0; // HOX!

        var_neighbor[v] = new int[temp_neighbor_count];
        var_neighbor_count[v]=temp_neighbor_count;

        count = 0;
        for(i=0; i<temp_neighbor_count; i++)
        {
            var_neighbor[v][count++] = temp_neighbor[i];
            neighbor_flag[temp_neighbor[i]] = 0;
        }
    }
    cout << "c built the neighbour relation" << endl;
}


void Satlike::allocate_memory()
{
    int malloc_var_length = num_vars+10;
    int malloc_clause_length = num_clauses+10;
    //int malloc_group_length = num_clauses+10;
    //
    clause_label_sat_count = new int [malloc_clause_length];
    label_criticality_count = new int [malloc_var_length];

    unit_clause = new lit[malloc_clause_length];

    var_lit          = new lit* [malloc_var_length];
    var_lit_count    = new int [malloc_var_length];
    clause_lit       = new lit* [malloc_clause_length];
    clause_lit_count = new int [malloc_clause_length];
    clause_type      = new int [malloc_clause_length];
    var_group        = new int* [malloc_var_length];
    var_group_count  = new int [malloc_var_length];
    
    var_label          = new lit* [malloc_var_length];
    var_label_count    = new int [malloc_var_length];

    clause_label       = new int[malloc_clause_length];
    clause_label_count = new int[malloc_clause_length];
    clause_labels      = new lit* [malloc_clause_length];
    sat_label          = new int[malloc_clause_length];

    score              = new long long [malloc_var_length];
    time_stamp         = new long long [malloc_var_length];
    label_cost         = new long long [malloc_var_length];
    configuration      = new int [malloc_var_length];
    var_neighbor       = new int* [malloc_var_length];
    var_neighbor_count = new int [malloc_var_length];
    neighbor_flag      = new int [malloc_var_length];
    temp_neighbor      = new int [malloc_var_length];

    org_clause_weight     = new long long [malloc_clause_length];
    clause_weight         = new long long [malloc_clause_length];
    sat_count             = new int [malloc_clause_length];
    sat_var               = new int [malloc_clause_length];
    clause_group          = new int [malloc_clause_length];

    /* allocate these elsewhere
    group_vars  = new int* [malloc_group_length];
    GM          = new int* [malloc_group_length];
    GB          = new int* [malloc_group_length];
    group_size  = new int  [malloc_group_length];
    */
    TSC         = new int  [malloc_var_length];

    goodvar_stack            = new int [malloc_var_length];
    already_in_goodvar_stack = new int[malloc_var_length];

    cur_soln       = new int [malloc_var_length];
    best_soln      = new int [malloc_var_length];
    local_opt_soln = new int [malloc_var_length];
    label_unsat_count = new int [malloc_var_length];

    large_weight_clauses                = new int [malloc_clause_length];
    label_large_weight_clauses          = new int [malloc_clause_length];
    already_in_label_large_weight_stack = new int [malloc_clause_length];

    temp_lit   = new int [malloc_var_length];
}


void Satlike::free_memory()
{
    int i;
    for (i = 0; i < num_clauses; i++)
        delete[] clause_lit[i];
    for (i = num_hclauses; i < num_clauses; i++)
        delete[] clause_labels[i];

    for(i=1; i<=num_vars; ++i)
    {
        delete[] var_lit[i];
        delete[] var_group[i];
        delete[] var_neighbor[i];
    }
    for(i=1; i <= num_groups; i++)
    {
        delete[] group_vars[i];
        delete[] GM[i];
        delete[] GS[i];
    }

    delete [] clause_label_sat_count;
    delete [] label_criticality_count;

    delete [] var_lit;
    delete [] var_lit_count;
    delete [] clause_lit;
    delete [] clause_lit_count;
    delete [] var_group;
    delete [] var_group_count;

    delete [] var_label;
    delete [] var_label_count;

    delete [] sat_label;
    delete [] clause_label_count;
    delete [] clause_labels;

    delete [] score;
    delete [] time_stamp;
    delete [] label_cost;
    delete [] configuration;
    delete [] var_neighbor;
    delete [] var_neighbor_count;
    delete [] neighbor_flag;
    delete [] temp_neighbor;

    delete [] org_clause_weight;
    delete [] clause_weight;
    delete [] sat_count;
    delete [] sat_var;
    delete [] clause_group;

    delete [] group_vars;
    delete [] GM;
    delete [] GS;
    delete [] GUC;
    delete [] TSC;
    delete [] group_type;
    delete [] group_size;
    delete [] group_weight;
    delete [] org_group_weight;
    delete [] best_soft_group;

    delete [] hardgroupunsat_stack;
    delete [] index_in_hardgroupunsat_stack;
    delete [] already_in_hardgroupunsat_stack;

    delete [] softgroupunsat_stack;
    delete [] index_in_softgroupunsat_stack;
    delete [] already_in_softgroupunsat_stack;

    delete [] labelgroupunsat_stack;
    delete [] index_in_labelgroupunsat_stack;
    delete [] already_in_labelgroupunsat_stack;

    delete [] best_label_group;
    delete [] group_selected_count;

    delete [] goodvar_stack;
    delete [] already_in_goodvar_stack;


    //delete [] fix;
    delete [] cur_soln;
    delete [] best_soln;
    delete [] local_opt_soln;
    delete [] label_unsat_count;

    delete [] large_weight_clauses;
    delete [] label_large_weight_clauses;
    delete [] already_in_label_large_weight_stack;

    delete [] temp_lit;

    delete maxpre;
    delete sat_solver;
}
