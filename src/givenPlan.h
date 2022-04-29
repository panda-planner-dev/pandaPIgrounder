#ifndef GIVEN_PLAN_H_INCLUDED
#define GIVEN_PLAN_H_INCLUDED

#include <string>
#include <unordered_map>
#include <unordered_set>
#include <set>
#include <vector>
#include "model.h"

struct given_plan_typing_information{
	std::unordered_map<int,std::set<std::vector<int>>> info;
	std::unordered_set<int> artificialTasks;
};

given_plan_typing_information extract_given_plan_typer(const Domain & domain, const Problem & problem,std::string planFile);


#endif
