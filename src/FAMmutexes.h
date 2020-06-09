#ifndef FAMMUTEX_H_INCLUDED
#define FAMMUTEX_H_INCLUDED

#include "model.h"
#include "sasinvariants.h"
#include "grounding.h"

std::vector<FAMGroup> compute_FAM_mutexes(const Domain & domain, const Problem & problem, grounding_configuration & config);

#endif
