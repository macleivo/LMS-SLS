#include "PriorityQueue.h"
#include <cassert>
#include <tuple>
#include <vector>
#include <iostream>
using namespace std;


template <typename T>
PriorityQueue<T>::PriorityQueue()
{
}


template <typename T>
PriorityQueue<T>::PriorityQueue(int maximum_size)
{
    max_size = 1;
    while(max_size <= maximum_size)
        max_size *= 2;

    priority_location.resize(1+max_size);
    pq.resize(1+max_size);

    pq_size = 0;
}


template <typename T>
void PriorityQueue<T>::resize(int maximum_size)
{
    max_size = 1;
    while(max_size <= maximum_size)
        max_size *= 2;

    priority_location.resize(1+max_size);
    pq.resize(1+max_size);

    pq_size = 0;
}


template <typename T>
void PriorityQueue<T>::heapify_down(int pq_pos)
{
    int hash;
    T   priority;
    std::tie(priority, hash) = pq.at(pq_pos);

    int l =     2*pq_pos;
    int r = 1 + 2*pq_pos;

    int b = l;
    while(l <= pq_size)
    {
        if(compare(pq.at(l).first, pq.at(r).first) > 0 && r <= pq_size)
            b = r;

        T   b_priority;
        int b_hash;
        std::tie(b_priority, b_hash) = pq.at(b);
        if(compare(b_priority, priority) >= 0)
            return;

        std::swap(pq.at(b), pq.at(pq_pos));
        std::swap(priority_location.at(b_hash), priority_location.at(hash));

        pq_pos = b;
        l =     2*pq_pos;
        r = 1 + 2*pq_pos;
        b = l;
    }
}


template <typename T>
void PriorityQueue<T>::heapify_up(int pq_pos)
{
    int hash;
    T   priority;
    std::tie(priority, hash) = pq.at(pq_pos);

    int a = pq_pos / 2;
    while(a >= 1)
    {
        T   a_priority;
        int a_hash;
        std::tie(a_priority, a_hash) = pq.at(a);
        if(compare(a_priority, priority) <= 0)
            return;

        std::swap(pq.at(a), pq.at(pq_pos));
        std::swap(priority_location.at(a_hash), priority_location.at(hash));

        pq_pos = a;
        a /= 2;
    }
}


template <typename T>
void PriorityQueue<T>::update_priority(T priority, int hash)
{
    assert(1 <= hash && hash <= max_size);

    int pq_pos       = priority_location.at(hash);
    T   old_priority = pq.at(pq_pos).first;

    if(compare(old_priority, priority) == 0)
        return;

    pq.at(pq_pos) = {priority, hash};
    if(compare(old_priority, priority) < 0) heapify_down(pq_pos);
    else heapify_up(pq_pos);
}


template <typename T>
void PriorityQueue<T>::push(T priority, int hash)
{
    assert(1 <= hash && hash <= max_size);
    if(priority_location.at(hash) > 0)
    {
        update_priority(priority, hash);
        return;
    }
    pq_size++;
    priority_location.at(hash) = pq_size;
    pq.at(pq_size) = {priority, hash};
    heapify_up(pq_size);
}


template <typename T>
void PriorityQueue<T>::pop(int hash)
{
    assert(pq_size > 0 && "Popping from an empty priority queue.");

    int pop_pos = 1;
    if(hash > 0)
    {
        if(priority_location.at(hash) == 0)
            return;
        pop_pos = priority_location.at(hash);
    }
    T pop_priority = pq.at(pop_pos).first;

    priority_location.at(pq.at(pq_size).second) = pop_pos;
    priority_location.at(pq.at(pop_pos).second) = 0;
    std::swap(pq.at(pop_pos), pq.at(pq_size));

    pq_size--;
    if(compare(pop_priority, pq.at(pop_pos).first) < 0)
        heapify_down(pop_pos);
    if(compare(pop_priority, pq.at(pop_pos).first) > 0)
        heapify_up(pop_pos);
}


template <typename T>
int PriorityQueue<T>::size()
{
    return pq_size;
}


template <typename T>
bool PriorityQueue<T>::empty()
{
    return pq_size == 0;
}

template <typename T>
void PriorityQueue<T>::clear()
{
    priority_location.clear();
    pq.clear();

    priority_location.resize(1+max_size);
    pq.resize(1+max_size);

    pq_size = 0;
}

template <typename T>
T PriorityQueue<T>::top_priority()
{
    assert(pq_size > 0);
    return pq.at(1).first;
}

template <typename T>
int PriorityQueue<T>::top()
{
    assert(pq_size > 0);
    return pq.at(1).second;
}

template <typename T>
bool PriorityQueue<T>::contains(int hash)
{
    assert(1 <= hash && hash <= max_size && "PriorityQueue: hash out of bounds in the method 'contains'");
    return priority_location.at(hash) > 0;
}

