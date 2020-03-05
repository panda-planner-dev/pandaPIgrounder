#include <string>
#include <iostream>
#include <algorithm>

#include "debug.h"
#include "FAMmutexes.h"
#include "pddl/pddl.h"


// CPDDL has dome defined functions that we simply copy. They should be static to not clutter the name space (their library contains them as well, but I want to have them in an extra file)
#include "cpddl.h"


// BOR_ERR_INIT produces gcc warnings which I cannot change ...
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wmissing-field-initializers"

std::pair<std::vector<int>,std::vector<int>> compute_local_type_hierarchy(const Domain & domain, const Problem & problem){
	// find subset relations between sorts
	
	// [i][j] = true means that j is a subset of i
	std::vector<std::vector<bool>> subset (domain.sorts.size());
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++)
			if (s1 != s2){
				if (std::includes(domain.sorts[s1].members.begin(), domain.sorts[s1].members.end(),
							domain.sorts[s2].members.begin(), domain.sorts[s2].members.end())){
					// here we know that s2 is a subset of s1
					subset[s1].push_back(true);
				} else
					subset[s1].push_back(false);
			} else subset[s1].push_back(false);

	// transitive reduction
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++)
			for (size_t s3 = 0; s3 < domain.sorts.size(); s3++)
				if (subset[s2][s1] && subset[s1][s3])
					subset[s2][s3] = false;
	
	
	DEBUG(for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++){
			if (subset[s1][s2]){
				std::cout << domain.sorts[s2].name;
				std::cout << " is a subset of ";
				std::cout << domain.sorts[s1].name;
				std::cout << std::endl;
			
			}
		}
	});

	// who is whose direct subset
	std::vector<std::vector<int>> directsubset (domain.sorts.size());
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++)
			if (subset[s1][s2])
				directsubset[s1].push_back(s2);
	
	// determine parents
	std::vector<int> parent (domain.sorts.size());
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		parent[s1] = -1;
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (size_t s2 = 0; s2 < domain.sorts.size(); s2++)
			if (subset[s1][s2]){
				if (parent[s2] != -1){
					std::cerr << "Type hierarchy is not a tree ... cpddl can't handle this. Exiting." << std::endl;
					exit(-1);
				}

				parent[s2] = s1;
			}


	DEBUG(for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		std::cout << domain.sorts[s1].name;
   		if (parent[s1] != -1) std::cout << " - " << domain.sorts[parent[s1]].name;
		std::cout << std::endl; 
	});

	// assign elements to sorts
	std::vector<std::set<int>> directElements (domain.sorts.size());
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		for (int elem : domain.sorts[s1].members){
			bool in_sub_sort = false;
			for (int s2 : directsubset[s1]){
				if (domain.sorts[s2].members.count(elem)){
					in_sub_sort = true;
					break;
				}
			}
			if (in_sub_sort) continue;
			directElements[s1].insert(elem);
		}
	}
	
	
	/*for (size_t s1 = 0; s1 < domain.sorts.size(); s1++){
		std::cout << domain.sorts[s1].name << ":";
		for (int e : directElements[s1]) std::cout << " " << domain.constants[e];
		std::cout << std::endl;
	}*/

	std::vector<int> sortOfElement (domain.constants.size());
	for (size_t c = 0; c < domain.constants.size(); c++)
		sortOfElement[c] = -1;
	
	for (size_t s1 = 0; s1 < domain.sorts.size(); s1++)
		for (int elem : directElements[s1]){
			if (sortOfElement[elem] != -1){
				std::cerr << "Sort is contained in two types .. this cannot happen. Thus must be a bug. Exiting." << std::endl;
				exit(1);
			}
			sortOfElement[elem] = s1;
		}

	return std::make_pair(parent,sortOfElement);	
} 


void topsortTypesCPDDL_dfs(int cur, std::vector<int> & parent,
						   std::vector<bool> & done, std::vector<int> & result){
	if (cur == -1) return;
	if (done[cur]) return;
	done[cur] = true;
	topsortTypesCPDDL_dfs(parent[cur],parent,done,result);
	result.push_back(cur);
}


std::vector<int> topsortTypesCPDDL(std::vector<int> & parent){
	std::vector<bool> done (parent.size());
	for (size_t i = 0; i < done.size(); i++) done[i] = false;

	std::vector<int> result;
	for (size_t i = 0; i < done.size(); i++)
		if (!done[i])
			topsortTypesCPDDL_dfs(i,parent,done,result);

	return result;
}


void cpddl_add_object_of_sort(pddl_t & pddl, const std::string & name, int type){
	pddl_obj_t * obj = pddlObjsAdd(&pddl.obj,name.c_str());
	obj->type = type;
	obj->is_constant = true;
	obj->is_private = 0;
	obj->owner = PDDL_OBJ_ID_UNDEF;
	obj->is_agent = 0;
}

pddl_cond_t* cpddl_create_atom(const PredicateWithArguments & lit, bool positive){
	pddl_cond_atom_t * atom = condAtomNew();
	atom->pred = lit.predicateNo + 1; // +1 for equals
	atom->arg_size = lit.arguments.size();
	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
	atom->neg = !positive;
	for (size_t i = 0; i < lit.arguments.size(); i++){
		atom->arg[i].param = lit.arguments[i];
		atom->arg[i].obj = PDDL_OBJ_ID_UNDEF;
	}
	return &atom->cls;
}

void cpddl_add_atom_to_conjunction(const PredicateWithArguments & lit, bool positive, pddl_cond_part_t * conj){
	condPartAdd(conj,cpddl_create_atom(lit,positive));
}

void cpddl_add_fact_to_conjunction(const Fact & f, pddl_cond_part_t * conj, const Domain & domain, pddl_t & pddl){
	pddl_cond_atom_t * atom = condAtomNew();
	atom->pred = f.predicateNo + 1; // +1 for equals
	atom->arg_size = f.arguments.size();
	atom->arg = BOR_ALLOC_ARR(pddl_cond_atom_arg_t, atom->arg_size);
	atom->neg = false;
	for (size_t i = 0; i < f.arguments.size(); i++){
		atom->arg[i].param = -1;
		atom->arg[i].obj = pddlObjsGet(&pddl.obj, domain.constants[f.arguments[i]].c_str()); 
	}
	condPartAdd(conj,&atom->cls);
}

void compute_FAM_mutexes(const Domain & domain, const Problem & problem, bool quietMode){
	// create representation of the domain/problem
	pddl_t pddl;
	bzero(&pddl,sizeof(pddl_t));
	std::string name = "dom";
	pddl.domain_name = const_cast<char*>(name.c_str());
	std::string name2 = "prob";
	pddl.problem_name = const_cast<char*>(name2.c_str());
	pddl.require = PDDL_REQUIRE_TYPING + PDDL_REQUIRE_CONDITIONAL_EFF;
	
	// compute a local type hierarchy
	auto [typeParents,objectType] = compute_local_type_hierarchy(domain,problem);
	
	// cpddl needs a root type named object
	pddlTypesAdd(&pddl.type,root_type_cppdl,-1);
	
	std::map<int,int> ourTypeIDToCPDDL;
	ourTypeIDToCPDDL[-1] = 0;
	for (int sort : topsortTypesCPDDL(typeParents)){
		int newID = ourTypeIDToCPDDL.size();
		ourTypeIDToCPDDL[sort] = newID;
		DEBUG(std::cout << "Adding sort " << sort << " (\"" << domain.sorts[sort].name << "\")" << std::endl);
		DEBUG(std::cout << "\tParent is " << typeParents[sort] << std::endl);
			// +1 is for the artificial root sort
		pddlTypesAdd(&pddl.type,domain.sorts[sort].name.c_str(),ourTypeIDToCPDDL[typeParents[sort]]);
	}
	
	
	bzero(&pddl.obj, sizeof(pddl.obj));
	pddl.obj.htable = borHTableNew(objHash, objEq, NULL);
	
	// add objects
	for (size_t o = 0; o < domain.constants.size(); o++)
		cpddl_add_object_of_sort(pddl,domain.constants[o], ourTypeIDToCPDDL[objectType[o]]);
	
/////////////////////////////////// COPIED FROM CPDDL/src/obj.c
    for (int i = 0; i < pddl.obj.obj_size; ++i){
        pddlTypesAddObj(&pddl.type, i, pddl.obj.obj[i].type);
	}
/////////////////////////////////// COPIED FROM CPDDL/src/obj.c

	// add equals predicate
/////////////////////////////////// COPIED FROM CPDDL/src/pred.c
    pddl.pred.eq_pred = -1;
    addEqPredicate(&pddl.pred);
/////////////////////////////////// COPIED FROM CPDDL/src/pred.c

	for (const Predicate & pred : domain.predicates){
		pddl_pred_t * p = pddlPredsAdd(&pddl.pred);
		p->name = BOR_STRDUP(pred.name.c_str());
		p->param_size = pred.argumentSorts.size();
    	p->param = BOR_REALLOC_ARR(p->param, int, p->param_size);
        for (size_t i = 0; i < pred.argumentSorts.size(); i++)
			p->param[i] = ourTypeIDToCPDDL[pred.argumentSorts[i]];
	}

	// add dummy predicate to avoid pruning
	pddl_pred_t * dumm_goal_predicate = pddlPredsAdd(&pddl.pred);
	dumm_goal_predicate->name = BOR_STRDUP("dummy-goal");
	dumm_goal_predicate->param_size = 0;
	dumm_goal_predicate->param = BOR_REALLOC_ARR(dumm_goal_predicate->param, int, dumm_goal_predicate->param_size);

	// add actions to the model
	for (size_t tid = 0; tid < domain.nPrimitiveTasks; tid++){
		const Task & t = domain.tasks[tid];
    	pddl_action_t *a;
    	a = pddlActionsAddEmpty(&pddl.action);
		a->name = BOR_STRDUP(t.name.c_str());

		int varidx = 0;
		for (const int & parameter : t.variableSorts){
			pddl_param_t * p = pddlParamsAdd(&(a->param));
			std::string paramName = "?var" + std::to_string(varidx++);
			p->name = BOR_STRDUP(paramName.c_str());
			p->type = ourTypeIDToCPDDL[parameter];
			p->is_agent = 0;
		}

		if (t.preconditions.size() + t.variableConstraints.size() == 0){
			a->pre = pddlCondNewEmptyAnd();
		} else {
			// add preconditions
			pddl_cond_part_t * pre_conj = condPartNew(PDDL_COND_AND);
			for (const PredicateWithArguments & pre : t.preconditions)
				cpddl_add_atom_to_conjunction(pre, true, pre_conj); // true = positive
			
			// add the variable constraints
			for (const VariableConstraint & vc : t.variableConstraints){
				PredicateWithArguments equalsLiteral;
				equalsLiteral.predicateNo = -1; // equals	
				equalsLiteral.arguments.clear();
				equalsLiteral.arguments.push_back(vc.var1);
				equalsLiteral.arguments.push_back(vc.var2);
				cpddl_add_atom_to_conjunction(equalsLiteral, vc.type == VariableConstraint::Type::EQUAL, pre_conj);
			}
			
			
			a->pre = &(pre_conj->cls);
			pddlCondSetPredRead(a->pre, &pddl.pred);
		}



		// effects
		pddl_cond_part_t * eff_conj = condPartNew(PDDL_COND_AND);
		PredicateWithArguments goalLiteral;
		goalLiteral.predicateNo = domain.predicates.size();	
		goalLiteral.arguments.clear();
		cpddl_add_atom_to_conjunction(goalLiteral, true, eff_conj);

		// unconditional add and delete effects
		for (auto & add : t.effectsAdd)
			cpddl_add_atom_to_conjunction(add, true, eff_conj);
		
		for (auto & del : t.effectsDel)
			cpddl_add_atom_to_conjunction(del, false, eff_conj);
		
		
		// copy conditional effects into data structure to handle them uniformly
		std::vector<std::pair<bool,std::pair<std::vector<PredicateWithArguments>, PredicateWithArguments>>> cond_eff;
		for (auto & add : t.conditionalAdd)
			cond_eff.push_back(std::make_pair(true,add));
		for (auto & del : t.conditionalDel)
			cond_eff.push_back(std::make_pair(false,del));

		for (auto & eff : cond_eff){
			pddl_cond_when_t * w = condNew(pddl_cond_when_t, PDDL_COND_WHEN);

			// build precondition of CE
			pddl_cond_part_t * pre_conj = condPartNew(PDDL_COND_AND);
			for (const PredicateWithArguments & pre : eff.second.first)
				cpddl_add_atom_to_conjunction(pre, true, pre_conj);
			w->pre = &pre_conj->cls;

			// build conditional effect
			w->eff = cpddl_create_atom(eff.second.second,eff.first);
			condPartAdd(eff_conj,&w->cls);
		}

		a->eff = &(eff_conj->cls);
		pddlCondSetPredReadWriteEff(a->eff, &pddl.pred);
	}





	//// PROBLEM DEFINITION

	// init
	pddl.init = condPartNew(PDDL_COND_AND);
	for (const Fact & f : problem.init)
		cpddl_add_fact_to_conjunction(f,pddl.init, domain, pddl);

	
	// set all atoms in into to be in init (else normalisation will not work)	
/////////////////////////////////// COPIED FROM CPDDL/src/pddl.c
	{
		pddl_cond_const_it_atom_t it;
    	const pddl_cond_atom_t *atom;
	    PDDL_COND_FOR_EACH_ATOM(&pddl.init->cls, &it, atom)
        	pddl.pred.pred[atom->pred].in_init = 1;
	}
/////////////////////////////////// COPIED FROM CPDDL/src/pddl.c


// goal
	pddl_cond_part_t * goal = condPartNew(PDDL_COND_AND);
	// artificial goal predicate
	Fact goalFact;
	goalFact.predicateNo = domain.predicates.size();
	goalFact.arguments.clear();
	cpddl_add_fact_to_conjunction(goalFact, goal, domain, pddl);

	for (const Fact & f : problem.goal)
		cpddl_add_fact_to_conjunction(f, goal, domain, pddl);
	pddl.goal = &(goal->cls);

	pddlTypesBuildObjTypeMap(&pddl.type, pddl.obj.obj_size);

	// Normalize pddl, i.e. remove stuff and so on
	pddlNormalize(&pddl);

	DEBUG(pddlPrintPDDLDomain(&pddl,stdout));
	DEBUG(pddlPrintPDDLProblem(&pddl,stdout));


	//////////////////// Mutex computation
	pddl_lifted_mgroups_infer_limits_t limits = PDDL_LIFTED_MGROUPS_INFER_LIMITS_INIT;
	limits.max_candidates = 10000;
	limits.max_mgroups = 10000;
	pddl_lifted_mgroups_t lifted_mgroups;
	pddlLiftedMGroupsInit(&lifted_mgroups);
	bor_err_t err = BOR_ERR_INIT;
	if (!quietMode)
		std::cout << "Computing Lifted FAM-Groups [Fiser, AAAI 2020]" << std::endl;
	pddlLiftedMGroupsInferFAMGroups(&pddl, &limits, &lifted_mgroups, &err);

	if (!quietMode)
		std::cout << "Found " << lifted_mgroups.mgroup_size << " Lifted FAM-Groups" << std::endl;

	DEBUG(for (int li = 0; li < lifted_mgroups.mgroup_size; ++li){
        fprintf(stdout, "M:%d: ", li);
        pddlLiftedMGroupPrint(&pddl, lifted_mgroups.mgroup + li, stdout);
    });

	exit(-1);
}

