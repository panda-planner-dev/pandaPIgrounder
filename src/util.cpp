#include <cassert>
#include "util.h"


void topsort_dfs(int a,std::vector<std::vector<int>> & adj, std::vector<int> & od, int & p, std::vector<int> & v) {
	assert(v[a]!=1);
	if(v[a]) return;
	v[a] = 1; // gray
	for(size_t i = 0; i < adj[a].size(); i++) topsort_dfs(adj[a][i],adj,od,p,v);
	v[a] = 2; // black
	od[p] = a; p--;
}

void topsort(std::vector<std::vector<int>> & adj, std::vector<int> & od) {
	int n = adj.size();
	std::vector<int> v(n);
	od.resize(n);
	for(int i = 0; i < n; i++) v[i]=0; //white
	int p=n-1;
	for(int i = 0; i < n; i++) if(!v[i]) topsort_dfs(i,adj,od,p,v);
}

