#pragma once

#include <tuple>
#include <vector>


template <class T>
class PriorityQueue
{
    private:
        int max_size;
        int pq_size = 0;

        std::vector<int> priority_location;
        std::vector<std::pair<T, int>> pq;

        void heapify_down(int pq_pos);
        void heapify_up(int pq_pos);
    public:
        PriorityQueue();
        PriorityQueue(int maximum_size);

        void update_priority(T priority, int hash);
        void push(T priority, int hash);
        void pop(int hash = -1);
        void clear();
        int  size();
        void resize(int maximum_size);
        bool empty();
        bool contains(int hash);

        int top();
        T   top_priority();

        int compare(T a, T b); // implemented by user
};
