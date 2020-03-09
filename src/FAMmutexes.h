#ifndef FAMMUTEX_H_INCLUDED
#define FAMMUTEX_H_INCLUDED

#include "model.h"
#include "sasinvariants.h"

std::vector<FAMGroup> compute_FAM_mutexes(const Domain & domain, const Problem & problem, bool quietMode);

#endif
