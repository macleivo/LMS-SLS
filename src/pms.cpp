#include "basis_pms.h"
#include "pms.h"
#include <signal.h>

static Satlike s;

/**
 * give the best answer we can when we receive a signal
 */
void interrupt(int sig)
{
    s.print_best_solution();
    s.free_memory();
    exit(10);
}

void interrupt2(int sig)
{
    s.print_best_solution();
    s.free_memory();
    exit(2);
}

int main(int argc, char* argv[])
{
    start_timing();
    cout<<"c this is satlike solver"<<endl;
    //Satlike s;
    signal(SIGTERM,interrupt);
    signal(SIGINT,interrupt2);
    signal(SIGKILL,interrupt2);
    signal(SIGXCPU,interrupt2);
    vector<int> init_solution;
    s.parse_params(argc, argv); //argv[1]);
    s.build_instance(); //argv[1]);
    s.local_search_with_decimation(init_solution,argv[1]);
    //s.simple_print();
    s.free_memory();

    return 0;
}
