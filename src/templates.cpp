#include "PriorityQueue.h"
#include "PriorityQueue.cpp"

template <>
int PriorityQueue<long long>::compare(long long a, long long b)
{
    if(a == b) return 0;
    if(a < b) return 1;
    return -1;
}

template class PriorityQueue<long long>;
