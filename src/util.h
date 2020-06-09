#ifndef UTIL_H_INCLUDED
#define UTIL_H_INCLUDED

#include <vector>
#include <unordered_set>	
#include <algorithm>	

void topsort(std::vector<std::vector<int>> & adj, std::vector<int> & od);

/// hash function s.t. conditional effects can be checked for duplicates
namespace std {
    template<> struct hash<std::pair<std::unordered_set<int>,int>>
    {
        std::size_t operator()(const std::pair<std::unordered_set<int>,int> & m) const noexcept
        {
			std::vector<int> v;
			for (const int & a : m.first) v.push_back(a);
			std::sort(v.begin(),v.end());
			std::size_t h = 0;
			for (const int & a : v) h = h*601 + a;
			h = h*601 + m.second;
			return h;
        }
    };

	template<> struct hash<std::pair<int,int>>
    {
        std::size_t operator()(const std::pair<int,int> & m) const noexcept
        {
			return m.first*100003 + m.second;
        }
    };
}
#endif
