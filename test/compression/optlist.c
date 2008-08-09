/***************************************************************************
*                       Command Line Option Parser
*
*   File    : optlist.c
*   Purpose : Provide getopt style command line option parsing
*   Author  : Michael Dipperstein
*   Date    : August 1, 2007
*
****************************************************************************
*   HISTORY
*
*   $Id: optlist.c,v 1.1.1.2 2007/09/04 04:45:42 michael Exp $
*   $Log: optlist.c,v $
*   Revision 1.1.1.2  2007/09/04 04:45:42  michael
*   Added FreeOptList.
*
*   Revision 1.1.1.1  2007/08/07 05:01:48  michael
*   Initial Release
*
****************************************************************************
*
* OptList: A command line option parsing library
* Copyright (C) 2007 by Michael Dipperstein (mdipper@alumni.engr.ucsb.edu)
*
* This file is part of the OptList library.
*
* OptList is free software; you can redistribute it and/or modify it
* under the terms of the GNU Lesser General Public License as published by
* the Free Software Foundation; either version 3 of the License, or (at
* your option) any later version.
*
* OptList is distributed in the hope that it will be useful, but
* WITHOUT ANY WARRANTY; without even the implied warranty of
* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Lesser
* General Public License for more details.
*
* You should have received a copy of the GNU Lesser General Public License
* along with this program.  If not, see <http://www.gnu.org/licenses/>.
*
***************************************************************************/

/***************************************************************************
*                             INCLUDED FILES
***************************************************************************/
#include "optlist.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/***************************************************************************
*                            TYPE DEFINITIONS
***************************************************************************/

/***************************************************************************
*                                CONSTANTS
***************************************************************************/

/***************************************************************************
*                            GLOBAL VARIABLES
***************************************************************************/

/***************************************************************************
*                               PROTOTYPES
***************************************************************************/
option_t *MakeOpt(const char option, char *const argument, const int index);

/***************************************************************************
*                                FUNCTIONS
***************************************************************************/

/****************************************************************************
*   Function   : GetOptList
*   Description: This function is similar to the POSIX function getopt.  All
*                options and their corresponding arguments are returned in a
*                linked list.  This function should only be called once per
*                an option list and it does not modify argv or argc.
*   Parameters : argc - the number of command line arguments (including the
*                       name of the executable)
*                argv - pointer to the open binary file to write encoded
*                       output
*                options - getopt style option list.  A NULL terminated
*                          string of single character options.  Follow an
*                          option with a colon to indicate that it requires
*                          an argument.
*   Effects    : Creates a link list of command line options and their
*                arguments.
*   Returned   : option_t type value where the option and arguement fields
*                contain the next option symbol and its argument (if any).
*                The argument field will be set to NULL if the option is
*                specified as having no arguments or no arguments are found.
*                The option field will be set to PO_NO_OPT if no more
*                options are found.
*
*   NOTE: The caller is responsible for freeing up the option list when it
*         is no longer needed.
****************************************************************************/
option_t *GetOptList(const int argc, char *const argv[], char *const options)
{
    int nextArg;
    option_t *head, *tail;
    int optIndex;

    /* start with first argument and nothing found */
    nextArg = 1;
    head = NULL;
    tail = NULL;

    /* loop through all of the command line arguments */
    while (nextArg < argc)
    {
        if ((strlen(argv[nextArg]) > 1) && ('-' == argv[nextArg][0]))
        {
            /* possible option */
            optIndex = 0;

            /* attempt to find a matching option */
            while ((options[optIndex] != '\0') &&
                (options[optIndex] != argv[nextArg][1]))
            {
                do
                {
                    optIndex++;
                }
                while ((options[optIndex] != '\0') &&
                    (':' == options[optIndex]));
            }

            if (options[optIndex] == argv[nextArg][1])
            {
                /* we found the matching option */
                if (NULL == head)
                {
                    head = MakeOpt(options[optIndex], NULL, OL_NOINDEX);
                    tail = head;
                }
                else
                {
                    tail->next = MakeOpt(options[optIndex], NULL, OL_NOINDEX);
                    tail = tail->next;
                }

                if (':' == options[optIndex + 1])
                {
                    /* the option found should have a text arguement */
                    if (strlen(argv[nextArg]) > 2)
                    {
                        /* no space between argument and option */
                        tail->argument = &(argv[nextArg][2]);
                        tail->argIndex = nextArg;
                    }
                    else if (nextArg < argc)
                    {
                        /* there must be space between the argument option */
                        nextArg++;
                        tail->argument = argv[nextArg];
                        tail->argIndex = nextArg;
                    }
                }
            }
        }

        nextArg++;
    }

    return head;
}

/****************************************************************************
*   Function   : MakeOpt
*   Description: This function uses malloc to allocate space for an option_t
*                type structure and initailizes the structure with the
*                values passed as a parameter.
*   Parameters : option - this option character
*                argument - pointer string containg the argument for option.
*                           Use NULL for no argument
*                index - argv[index] contains argument us OL_NOINDEX for
*                        no argument
*   Effects    : A new option_t type variable is created on the heap.
*   Returned   : Pointer to newly created and initialized option_t type
*                structure.  NULL if space for structure can't be allocated.
****************************************************************************/
option_t *MakeOpt(const char option, char *const argument, const int index)
{
    option_t *opt;

    opt = malloc(sizeof(option_t));

    if (opt != NULL)
    {
        opt->option = option;
        opt->argument = argument;
        opt->argIndex = index;
        opt->next = NULL;
    }
    else
    {
        perror("Failed to Allocate option_t");
    }

    return opt;
}

/****************************************************************************
*   Function   : FreeOptList
*   Description: This function will free all the elements in an option_t
*                type linked list starting from the node passed as a
*                parameter.
*   Parameters : list - head of linked list to be freed
*   Effects    : All elements of the linked list pointed to by list will
*                be freed and list will be set to NULL.
*   Returned   : None
****************************************************************************/
void FreeOptList(option_t *list)
{
    option_t *head, *next;

    head = list;
    list = NULL;

    while (head != NULL)
    {
        next = head->next;
        free(head);
        head = next;
    }

    return;
}
