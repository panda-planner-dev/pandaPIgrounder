#include "naiveGrounding.h"

#include <iostream>
#include <map>
#include <set>

using namespace std;


struct TaskGroundInstance{
	int task;
	vector<int> args;
	
	vector<int> pre,add,del;
};

struct GroundFact{
	int pred;
	vector<int> args;

};

bool operator <(const GroundFact& x, const GroundFact& y) {
	if (x.pred < y.pred) return true;
	if (x.pred > y.pred) return false;

	if (x.args < y.args) return true;
	return false;
}

vector<TaskGroundInstance> naivelyGroundTask(Domain & domain, int task, int vPos){
	if (vPos == int(domain.tasks[task].variableSorts.size())){
		TaskGroundInstance inst;
		inst.task = task;
		vector<TaskGroundInstance> ret;
		ret.push_back(inst);
		return ret;
	}

	// get instances of next layer
	vector<TaskGroundInstance> nextG = naivelyGroundTask (domain, task, vPos+1);

	// iterate through constants for that variable
	int vSort = domain.tasks[task].variableSorts[vPos];
	vector<TaskGroundInstance> ret;
	for (unsigned int inSortIndex = 0; inSortIndex < domain.sorts[vSort].members.size(); inSortIndex++){
		int c = domain.sorts[vSort].members[inSortIndex];
		for (unsigned int og = 0; og < nextG.size(); og++){
			TaskGroundInstance inst;
			inst.task = task;
			inst.args.push_back(c);
			for (unsigned int arg = 0; arg < nextG[og].args.size(); arg++)
				inst.args.push_back(nextG[og].args[arg]);
			
			// if we are root check constraint consistency
			if (vPos == 0){
				bool failed = false;
				for (unsigned constr = 0; constr < domain.tasks[task].variableConstraints.size(); constr++){
					VariableConstraint con = domain.tasks[task].variableConstraints[constr];
					int c1 = inst.args[con.var1];
					int c2 = inst.args[con.var2];
					if (con.type == VariableConstraint::Type::EQUAL && c1 != c2) failed = true;
					if (con.type == VariableConstraint::Type::NOT_EQUAL && c1 == c2) failed = true;
				}
				if (failed) continue;
			
			}
			ret.push_back(inst);
		}
	}

	return ret;
}


int numForFact(map<GroundFact,int> & fti, Domain & domain, TaskGroundInstance & gt, PredicateWithArguments & arg){
	GroundFact gf;
	gf.pred = arg.predicateNo;
	for (unsigned int argc = 0;  argc < arg.arguments.size(); argc++)
		gf.args.push_back(gt.args[arg.arguments[argc]]);
  
	if (!fti.count(gf)) fti[gf] = fti.size();
	return fti[gf];
}



void naiveGrounding(Domain & domain, Problem & problem){
	// 1. fully instantiate all primitive tasks
	vector<TaskGroundInstance> allInst;
	
	for (int t = 0; t < domain.nPrimitiveTasks; t++){
		vector<TaskGroundInstance> gs = naivelyGroundTask(domain,t,0);
		for (unsigned int g = 0; g < gs.size(); g++)
			allInst.push_back(gs[g]);
	}
	//cout << allInst.size() << endl;


	map<GroundFact,int> fti;
	// compute all ground facts
	for (int gt = 0; gt < int(allInst.size()); gt++){
		for (int pre = 0; pre < int(domain.tasks[allInst[gt].task].preconditions.size()); pre++)
			allInst[gt].pre.push_back(numForFact(fti, domain, allInst[gt], domain.tasks[allInst[gt].task].preconditions[pre]));
		for (int add = 0; add < int(domain.tasks[allInst[gt].task].effectsAdd.size()); add++)
			allInst[gt].add.push_back(numForFact(fti, domain, allInst[gt], domain.tasks[allInst[gt].task].effectsAdd[add]));
		for (int del = 0; del < int(domain.tasks[allInst[gt].task].effectsDel.size()); del++)
			allInst[gt].del.push_back(numForFact(fti, domain, allInst[gt], domain.tasks[allInst[gt].task].effectsDel[del]));
	}



	// and translate the initial state
	set<int> state;
	for (unsigned int init = 0; init < problem.init.size(); init++){
		GroundFact gf;
		gf.pred = problem.init[init].predicateNo;
		gf.args = problem.init[init].arguments;
		
		if (!fti.count(gf)) fti[gf] = fti.size();

		state.insert(fti[gf]);
		/*cout << "INIT " << fti[gf];
		cout << " " << domain.predicates[gf.pred].name;
		for (int a : gf.args) cout << " " << domain.constants[a];
		cout << endl;*/
	}



	// run PG in very slow time
	vector<bool> appli (int(allInst.size()));
	for (int gt = 0; gt < int(allInst.size()); gt++) appli[gt] = false; 
	int cappli = 0;

	bool changed = true;
	while (changed){
		changed = false;
		// go over all gts
		for (int gt = 0; gt < int(allInst.size()); gt++){
			if (appli[gt]) continue;
			// check prec
			bool all = true;
			for (int p : allInst[gt].pre) all &= state.count(p) != 0;
			if (!all) continue;
			
			appli[gt] = true;
			cappli++;
			for (int p : allInst[gt].add){
				if (state.count(p)) continue;
				changed = true;
				state.insert(p);
			}
		}
	}

	cout << cappli << " " << state.size() << endl;
	for (int gt = 0; gt < int(allInst.size()); gt++){
		if (!appli[gt]) continue;
		//if (appli[gt]) cout << "!  ";
		cout << domain.tasks[allInst[gt].task].name;
		for (unsigned int arg = 0; arg < allInst[gt].args.size(); arg++)
			cout << " " << domain.constants[allInst[gt].args[arg]];
		
		//for (int pp : allInst[gt].pre) cout << " " << pp;
		//for (int pp : allInst[gt].add) cout << " +" << pp;

		cout << endl;
	}


	for (auto e : fti){
		if (!state.count(e.second)) continue;
		cout << domain.predicates[e.first.pred].name;
		for (int a : e.first.args) cout << " " << domain.constants[a];
		cout << endl;
	}	


	return;
}
