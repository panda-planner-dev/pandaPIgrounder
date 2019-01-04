#include <string>

#include "model.h"

BadInputException::BadInputException (std::string message) : message (message)
{
}

const char * BadInputException::what () const throw ()
{
	return message.c_str ();
}
