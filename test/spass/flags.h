/**************************************************************/
/* ********************************************************** */
/* *                                                        * */
/* *                 FLAGS OF SPASS                         * */
/* *                                                        * */
/* *  $Module:   FLAGS                                      * */ 
/* *                                                        * */
/* *  Copyright (C) 1996, 1997, 1998, 1999, 2000, 2001      * */
/* *  MPI fuer Informatik                                   * */
/* *                                                        * */
/* *  This program is free software; you can redistribute   * */
/* *  it and/or modify it under the terms of the GNU        * */
/* *  General Public License as published by the Free       * */
/* *  Software Foundation; either version 2 of the License, * */
/* *  or (at your option) any later version.                * */
/* *                                                        * */
/* *  This program is distributed in the hope that it will  * */
/* *  be useful, but WITHOUT ANY WARRANTY; without even     * */
/* *  the implied warranty of MERCHANTABILITY or FITNESS    * */
/* *  FOR A PARTICULAR PURPOSE.  See the GNU General Public * */
/* *  License for more details.                             * */
/* *                                                        * */
/* *  You should have received a copy of the GNU General    * */
/* *  Public License along with this program; if not, write * */
/* *  to the Free Software Foundation, Inc., 59 Temple      * */
/* *  Place, Suite 330, Boston, MA  02111-1307  USA         * */
/* *                                                        * */
/* *                                                        * */
/* $Revision: 21527 $                                        * */
/* $State$                                            * */
/* $Date: 2005-04-24 21:10:28 -0700 (Sun, 24 Apr 2005) $                             * */
/* $Author: duraid $                                       * */
/* *                                                        * */
/* *             Contact:                                   * */
/* *             Christoph Weidenbach                       * */
/* *             MPI fuer Informatik                        * */
/* *             Stuhlsatzenhausweg 85                      * */
/* *             66123 Saarbruecken                         * */
/* *             Email: weidenb@mpi-sb.mpg.de               * */
/* *             Germany                                    * */
/* *                                                        * */
/* ********************************************************** */
/**************************************************************/


/* $RCSfile$ */

#ifndef _FLAGS_
#define _FLAGS_

#include <limits.h>
#include <stdio.h>

#include "memory.h"
#include "misc.h"

/**************************************************************/
/* Data Structures and Constants                              */
/**************************************************************/

extern const int flag_CLEAN;

/* Define the legal values for all flags as data types.
  
   All flags have a minimum and a maximum. Legal values are 
   within that range, *excluding* the minimum, maximum value. By using 
   flag_XXXMIN and flag_XXXMAX we have a simple test for a 
   flag's correctness:

     if
       flag value <= flag minimum 
       or flag value >= flag maximum
     then
       the flag has an illegal state.

   Boolean flags have two legal values:
    * flag_XXXOFF ( = 0)
    * flag_XXXON ( = 1)
*/

/* State definitions for boolean flags */
typedef enum { flag_OFF = 0,
	       flag_ON  = 1
} FLAG_BOOLEAN;

/* State definitions for flag_APPLYDEFS */
typedef enum { flag_APPLYDEFSMIN = -1,
               flag_APPLYDEFSOFF = flag_OFF,
               flag_APPLYDEFSMAX = INT_MAX
} FLAG_APPLYDEFSTYPE;

/* State definitions for flag_AUTO */
typedef enum { flag_AUTOMIN = -1,
	       flag_AUTOOFF = flag_OFF,
	       flag_AUTOON  = flag_ON,
	       flag_AUTOMAX
} FLAG_AUTOTYPE;

/* State definitions for flag_BOUNDLOOPS */
typedef enum { flag_BOUNDLOOPSMIN = 0,
	       flag_BOUNDLOOPSMAX = INT_MAX
} FLAG_BOUNDLOOPSTYPE;

/* State definitions for flag_BOUNDMODE */
typedef enum { flag_BOUNDMODEMIN = -1,
	       flag_BOUNDMODEUNLIMITED,
	       flag_BOUNDMODERESTRICTEDBYWEIGHT, 
	       flag_BOUNDMODERESTRICTEDBYDEPTH,
	       flag_BOUNDMODEMAX
} FLAG_BOUNDMODETYPE;

/* State definitions for flag_BOUNDSTART */
typedef enum { flag_BOUNDSTARTMIN = -2,
	       flag_BOUNDSTARTUNLIMITED,
	       flag_BOUNDSTARTMAX = INT_MAX
} FLAG_BOUNDSTARTTYPE;

/* State definitions for flag_CNFFEQREDUCTIONS */
typedef enum { flag_CNFFEQREDUCTIONSMIN = -1,
               flag_CNFFEQREDUCTIONSOFF = flag_OFF,
               flag_CNFFEQREDUCTIONSON  = flag_ON,
               flag_CNFFEQREDUCTIONSMAX
} FLAG_CNFFEQREDUCTIONSTYPE;

/* State definitions for flag_CNFOPTSKOLEM */
typedef enum { flag_CNFOPTSKOLEMMIN = -1,
               flag_CNFOPTSKOLEMOFF = flag_OFF,
               flag_CNFOPTSKOLEMON  = flag_ON,
               flag_CNFOPTSKOLEMMAX
} flag_CNFOPTSKOLEMTYPE;

/* State definitions for flag_CNFPRENAMING */
typedef enum { flag_CNFPRENAMINGMIN = -1,
               flag_CNFPRENAMINGOFF = flag_OFF,
               flag_CNFPRENAMINGON  = flag_ON,
               flag_CNFPRENAMINGMAX
} FLAG_CNFPRENAMINGTYPE;

/* State definitions for flag_CNFPROOFSTEPS */
typedef enum { flag_CNFPROOFSTEPSMIN = 0,
	       flag_CNFPROOFSTEPSMAX = INT_MAX
} FLAG_CNFPROOFSTEPSTYPE;

/* State definitions for flag_CNFRENAMING */
typedef enum { flag_CNFRENAMINGMIN = -1,
               flag_CNFRENAMINGOFF = flag_OFF,
               flag_CNFRENAMINGON  = flag_ON,
               flag_CNFRENAMINGMAX
} FLAG_CNFRENAMINGTYPE;

/* State definitions for flag_CNFSTRSKOLEM */
typedef enum { flag_CNFSTRSKOLEMMIN = -1,
               flag_CNFSTRSKOLEMOFF = flag_OFF,
               flag_CNFSTRSKOLEMON  = flag_ON,
               flag_CNFSTRSKOLEMMAX
} FLAG_CNFSTRSKOLEMTYPE;

/* State definitions for flag_DOCPROOF */
typedef enum { flag_DOCPROOFMIN = -1,
	       flag_DOCPROOFOFF = flag_OFF,
	       flag_DOCPROOFON  = flag_ON,
	       flag_DOCPROOFMAX
} FLAG_DOCPROOFTYPE;

/* State definitions for flag_DOCSPLIT */
typedef enum { flag_DOCSPLITMIN = -1,
	       flag_DOCSPLITOFF = flag_OFF,
	       flag_DOCSPLITON  = flag_ON,
	       flag_DOCSPLITMAX
} FLAG_DOCSPLITTYPE;

/* State definitions for flag_DOCSST */
typedef enum { flag_DOCSSTMIN = -1,
	       flag_DOCSSTOFF = flag_OFF,
	       flag_DOCSSTON  = flag_ON,
	       flag_DOCSSTMAX
} FLAG_DOCSSTTYPE;

/* State definitions for flag_FLOTTER */
typedef enum { flag_FLOTTERMIN = -1,
	       flag_FLOTTEROFF = flag_OFF,
	       flag_FLOTTERON  = flag_ON,
	       flag_FLOTTERMAX
} FLAG_FLOTTERTYPE;

/* State definitions for flag_FPDFGPROOF */
typedef enum { flag_FPDFGPROOFMIN = -1,
               flag_FPDFGPROOFOFF = flag_OFF,
               flag_FPDFGPROOFON  = flag_ON,
               flag_FPDFGPROOFMAX
} FLAG_FPDFGPROOFTYPE;

/* State definitions for flag_FPMODEL */
typedef enum { flag_FPMODELMIN = -1,
	       flag_FPMODELOFF = flag_OFF,
	       flag_FPMODELALLCLAUSES,
	       flag_FPMODELPOTENTIALLYPRODUCTIVECLAUSES,
	       flag_FPMODELMAX
} FLAG_FPMODELTYPE;

/* State definitions for flag_FULLRED */
typedef enum { flag_FULLREDMIN = -1,
               flag_FULLREDOFF = flag_OFF,
               flag_FULLREDON  = flag_ON,
               flag_FULLREDMAX
} FLAG_FULLREDTYPE;

/* State definitions for flag_FUNCWEIGHT */
typedef enum { flag_FUNCWEIGHTMIN = 0,
	       flag_FUNCWEIGHTMAX = INT_MAX
} FLAG_FUNCWEIGHTTYPE;

/* State definitions for flag_IBUR */
typedef enum { flag_BOUNDEDDEPTHUNITRESOLUTIONMIN = -1,
               flag_BOUNDEDDEPTHUNITRESOLUTIONOFF = flag_OFF,
               flag_BOUNDEDDEPTHUNITRESOLUTIONON  = flag_ON,
               flag_BOUNDEDDEPTHUNITRESOLUTIONMAX
} FLAG_IBURTYPE;

/* State definitions for flag_IDEF */
typedef enum { flag_DEFINITIONAPPLICATIONMIN = -1,
               flag_DEFINITIONAPPLICATIONOFF = flag_OFF,
               flag_DEFINITIONAPPLICATIONON  = flag_ON,
               flag_DEFINITIONAPPLICATIONMAX
} FLAG_IDEFTYPE;

/* State definitions for flag_IEMS */
typedef enum { flag_EMPTYSORTMIN = -1,
               flag_EMPTYSORTOFF = flag_OFF,
               flag_EMPTYSORTON  = flag_ON,
               flag_EMPTYSORTMAX
} FLAG_IEMSTYPE;

/* State definitions for flag_IEQF */
typedef enum { flag_EQUALITYFACTORINGMIN = -1,
               flag_EQUALITYFACTORINGOFF = flag_OFF,
               flag_EQUALITYFACTORINGON  = flag_ON,
               flag_EQUALITYFACTORINGMAX
} FLAG_IEQFTYPE;

/* State definitions for flag_IEQR */
typedef enum { flag_EQUALITYRESOLUTIONMIN = -1,
               flag_EQUALITYRESOLUTIONOFF = flag_OFF,
               flag_EQUALITYRESOLUTIONON  = flag_ON,
               flag_EQUALITYRESOLUTIONMAX
} FLAG_IEQRTYPE;

/* State definitions for flag_IERR */
typedef enum { flag_REFLEXIVITYRESOLUTIONMIN = -1,
               flag_REFLEXIVITYRESOLUTIONOFF = flag_OFF,
               flag_REFLEXIVITYRESOLUTIONON  = flag_ON,
               flag_REFLEXIVITYRESOLUTIONMAX
} FLAG_IERRTYPE;

/* State definitions for flag_IMPM */
typedef enum { flag_MERGINGPARAMODULATIONMIN = -1,
               flag_MERGINGPARAMODULATIONOFF = flag_OFF,
               flag_MERGINGPARAMODULATIONON  = flag_ON,
               flag_MERGINGPARAMODULATIONMAX
} FLAG_IMPMTYPE;

/* State definitions for flag_INTERACTIVE */
typedef enum { flag_INTERACTIVEMIN = -1,
	       flag_INTERACTIVEOFF = flag_OFF,
	       flag_INTERACTIVEON  = flag_ON,
	       flag_INTERACTIVEMAX
} FLAG_INTERACTIVETYPE;

/* State definitions for flag_IOFC */
typedef enum { flag_FACTORINGMIN = -1,
	       flag_FACTORINGOFF = flag_OFF,
	       flag_FACTORINGONLYRIGHT,
	       flag_FACTORINGRIGHTANDLEFT,
	       flag_FACTORINGMAX
} FLAG_IOFCTYPE;

/* State definitions for flag_IOHY */
typedef enum { flag_ORDEREDHYPERRESOLUTIONMIN = -1,
               flag_ORDEREDHYPERRESOLUTIONOFF = flag_OFF,
               flag_ORDEREDHYPERRESOLUTIONON  = flag_ON,
               flag_ORDEREDHYPERRESOLUTIONMAX
} FLAG_IOHYTYPE;

/* State definitions for flag_IOPM */
typedef enum { flag_ORDEREDPARAMODULATIONMIN = -1,
               flag_ORDEREDPARAMODULATIONOFF = flag_OFF,
               flag_ORDEREDPARAMODULATIONON  = flag_ON,
               flag_ORDEREDPARAMODULATIONMAX
} FLAG_IOPMTYPE;

/* State definitions for flag_IORE */
typedef enum { flag_ORDEREDRESOLUTIONMIN = -1,
	       flag_ORDEREDRESOLUTIONOFF = flag_OFF,
	       flag_ORDEREDRESOLUTIONNOEQUATIONS,
	       flag_ORDEREDRESOLUTIONWITHEQUATIONS,
	       flag_ORDEREDRESOLUTIONMAX
} FLAG_IORETYPE;

/* State definitions for flag_ISFC */
typedef enum { flag_STANDARDFACTORINGMIN = -1,
	       flag_STANDARDFACTORINGOFF = flag_OFF,
	       flag_STANDARDFACTORINGON  = flag_ON,
	       flag_STANDARDFACTORINGMAX
} FLAG_ISFCTYPE;

/* State definitions for flag_ISHY */
typedef enum { flag_STANDARDHYPERRESOLUTIONMIN = -1,
               flag_STANDARDHYPERRESOLUTIONOFF = flag_OFF,
               flag_STANDARDHYPERRESOLUTIONON  = flag_ON,
               flag_STANDARDHYPERRESOLUTIONMAX
} FLAG_ISHYTYPE;

/* State definitions for flag_ISOR */
typedef enum { flag_SORTRESOLUTIONMIN = -1,
               flag_SORTRESOLUTIONOFF = flag_OFF,
               flag_SORTRESOLUTIONON  = flag_ON,
               flag_SORTRESOLUTIONMAX
} FLAG_ISORTYPE;

/* State definitions for flag_ISPL */
typedef enum { flag_SUPERPOSITIONLEFTMIN = -1,
               flag_SUPERPOSITIONLEFTOFF = flag_OFF,
               flag_SUPERPOSITIONLEFTON  = flag_ON,
               flag_SUPERPOSITIONLEFTMAX
} FLAG_ISPLTYPE;

/* State definitions for flag_ISPM */
typedef enum { flag_STANDARDPARAMODULATIONMIN = -1,
               flag_STANDARDPARAMODULATIONOFF = flag_OFF,
               flag_STANDARDPARAMODULATIONON  = flag_ON,
               flag_STANDARDPARAMODULATIONMAX
} FLAG_ISPMTYPE;

/* State definitions for flag_ISPR */
typedef enum { flag_SUPERPOSITIONRIGHTMIN = -1,
               flag_SUPERPOSITIONRIGHTOFF = flag_OFF,
               flag_SUPERPOSITIONRIGHTON  = flag_ON,
               flag_SUPERPOSITIONRIGHTMAX
} FLAG_ISPRTYPE;

/* State definitions for flag_ISRE */
typedef enum { flag_STANDARDRESOLUTIONMIN = -1,
	       flag_STANDARDRESOLUTIONOFF = flag_OFF,
	       flag_STANDARDRESOLUTIONNOEQUATIONS,
	       flag_STANDARDRESOLUTIONWITHEQUATIONS,
	       flag_STANDARDRESOLUTIONMAX
} FLAG_ISRETYPE;

/* State definitions for flag_IUNR */
typedef enum { flag_UNITRESOLUTIONMIN = -1,
               flag_UNITRESOLUTIONOFF = flag_OFF,
               flag_UNITRESOLUTIONON  = flag_ON,
               flag_UNITRESOLUTIONMAX
} FLAG_IUNRTYPE;

/* State definitions for flag_IURR */
typedef enum { flag_UNITRESULTINGRESOLUTIONMIN = -1,
               flag_UNITRESULTINGRESOLUTIONOFF = flag_OFF,
               flag_UNITRESULTINGRESOLUTIONON  = flag_ON,
               flag_UNITRESULTINGRESOLUTIONMAX
} FLAG_IURRTYPE;

/* State definitions for flag_LOOPS */
typedef enum { flag_LOOPSMIN = -2,
	       flag_LOOPSUNLIMITED,
	       flag_LOOPSMAX = INT_MAX
} FLAG_LOOPSTYPE;

/* State definitions for flag_MEMORY */
typedef enum { flag_MEMORYMIN = -2,
	       flag_MEMORYUNLIMITED,
	       flag_MEMORYMAX = INT_MAX
} FLAG_MEMORYTYPE;

/* State definitions for flag_ORD */
typedef enum { flag_ORDMIN = -1,
	       flag_ORDKBO, 
	       flag_ORDRPOS,
	       flag_ORDMAX
} FLAG_ORDTYPE;

/* State definitions for flag_PAPPLYDEFS */
typedef enum { flag_PAPPLYDEFSMIN = -1,
               flag_PAPPLYDEFSOFF = flag_OFF,
               flag_PAPPLYDEFSON  = flag_ON,
               flag_PAPPLYDEFSMAX
} FLAG_PAPPLYDEFSTYPE;

/* State definitions for flag_PBDC */
typedef enum { flag_PBDCMIN = -1,
               flag_PBDCOFF = flag_OFF,
               flag_PBDCON  = flag_ON,
               flag_PBDCMAX
} FLAG_PBDCTYPE;

/* State definitions for flag_PBINC */
typedef enum { flag_PBINCMIN = -1,
               flag_PBINCOFF = flag_OFF,
               flag_PBINCON  = flag_ON,
               flag_PBINCMAX
} FLAG_PBINCTYPE;

/* State definitions for flag_PMRR */
typedef enum { flag_PMRRMIN = -1,
	       flag_PMRROFF = flag_OFF,
	       flag_PMRRON  = flag_ON,
	       flag_PMRRMAX
} FLAG_PMRRTYPE;

/* State definitions for flag_PCON */
typedef enum { flag_PCONMIN = -1,
	       flag_PCONOFF = flag_OFF,
	       flag_PCONON  = flag_ON,
	       flag_PCONMAX
} FLAG_PCONTYPE;

/* State definitions for flag_PDER */
typedef enum { flag_PDERMIN = -1,
	       flag_PDEROFF = flag_OFF,
	       flag_PDERON  = flag_ON,
	       flag_PDERMAX
} FLAG_PDERTYPE;

/* State definitions for flag_PEMPTYCLAUSE */
typedef enum { flag_PEMPTYCLAUSEMIN = -1,
	       flag_PEMPTYCLAUSEOFF = flag_OFF,
	       flag_PEMPTYCLAUSEON  = flag_ON,
	       flag_PEMPTYCLAUSEMAX
} FLAG_PEMPTYCLAUSETYPE;

/* State definitions for flag_PFLAGS */
typedef enum { flag_PFLAGSMIN = -1,
               flag_PFLAGSOFF = flag_OFF,
               flag_PFLAGSON  = flag_ON,
               flag_PFLAGSMAX
} FLAG_PFLAGSTYPE;

/* State definitions for flag_PGIVEN */
typedef enum { flag_PGIVENMIN = -1,
	       flag_PGIVENOFF = flag_OFF,
	       flag_PGIVENON  = flag_ON,
	       flag_PGIVENMAX
} FLAG_PGIVENTYPE;

/* State definitions for flag_PKEPT */
typedef enum { flag_PKEPTMIN = -1,
	       flag_PKEPTOFF = flag_OFF,
	       flag_PKEPTON  = flag_ON,
	       flag_PKEPTMAX
} FLAG_PKEPTTYPE;

/* State definitions for flag_PLABELS */
typedef enum { flag_PLABELSMIN = -1,
	       flag_PLABELSOFF = flag_OFF,
	       flag_PLABELSON  = flag_ON,
	       flag_PLABELSMAX
} FLAG_PLABELSTYPE;

/* State definitions for flag_POBV */
typedef enum { flag_POBVMIN = -1,
	       flag_POBVOFF = flag_OFF,
	       flag_POBVON  = flag_ON,
	       flag_POBVMAX
} FLAG_POBVTYPE;

/* State definitions for flag_POPTSKOLEM */
typedef enum { flag_POPTSKOLEMMIN = -1,
               flag_POPTSKOLEMOFF = flag_OFF,
               flag_POPTSKOLEMON  = flag_ON,
               flag_POPTSKOLEMMAX
} FLAG_POPTSKOLEMTYPE;

/* State definitions for flag_PPROBLEM */
typedef enum { flag_PPROBLEMMIN = -1,
	       flag_PPROBLEMOFF = flag_OFF,
	       flag_PPROBLEMON  = flag_ON,
	       flag_PPROBLEMMAX
} FLAG_PPROBLEMTYPE;

/* State definitions for flag_PREFCON */
typedef enum { flag_PREFCONMIN = 0,
	       flag_PREFCONUNCHANGED,
	       flag_PREFCONMAX = INT_MAX
} FLAG_PREFCONTYPE;

/* State definitions for flag_PREFVAR */
typedef enum { flag_PREFVARMIN = -1,
               flag_PREFVAROFF = flag_OFF,
               flag_PREFVARON  = flag_ON,
               flag_PREFVARMAX
} FLAG_PREFVARTYPE;

/* State definitions for flag_PREW */
typedef enum { flag_PREWMIN = -1,
	       flag_PREWOFF = flag_OFF,
	       flag_PREWON  = flag_ON,
	       flag_PREWMAX
} FLAG_PREWTYPE;

/* State definitions for flag_PCRW */
typedef enum { flag_PCRWMIN = -1,
	       flag_PCRWOFF = flag_OFF,
	       flag_PCRWON  = flag_ON,
	       flag_PCRWMAX
} FLAG_PCRWTYPE;

/* State definitions for flag_PAED */
typedef enum { flag_PAEDMIN = -1,
	       flag_PAEDOFF = flag_OFF,
	       flag_PAEDON  = flag_ON,
	       flag_PAEDMAX
} FLAG_PAEDTYPE;

/* State definitions for flag_PSSI */
typedef enum { flag_PSSIMIN = -1,
	       flag_PSSIOFF = flag_OFF,
	       flag_PSSION  = flag_ON,
	       flag_PSSIMAX
} FLAG_PSSITYPE;

/* State definitions for flag_PSST */
typedef enum { flag_PSSTMIN = -1,
	       flag_PSSTOFF = flag_OFF,
	       flag_PSSTON  = flag_ON,
	       flag_PSSTMAX
} FLAG_PSSTTYPE;

/* State definitions for flag_PSTATISTIC */
typedef enum { flag_PSTATISTICMIN = -1,
               flag_PSTATISTICOFF = flag_OFF,
               flag_PSTATISTICON  = flag_ON,
               flag_PSTATISTICMAX
} FLAG_PSTATISTICTYPE;

/* State definitions for flag_PSTRSKOLEM */
typedef enum { flag_PSTRSKOLEMMIN = -1,
               flag_PSTRSKOLEMOFF = flag_OFF,
               flag_PSTRSKOLEMON  = flag_ON,
               flag_PSTRSKOLEMMAX
} FLAG_PSTRSKOLEMTYPE;

/* State definitions for flag_PSUB */
typedef enum { flag_PSUBMIN = -1,
	       flag_PSUBOFF = flag_OFF,
	       flag_PSUBON  = flag_ON,
	       flag_PSUBMAX
} FLAG_PSUBTYPE;

/* State definitions for flag_PTAUT */
typedef enum { flag_PTAUTMIN = -1,
	       flag_PTAUTOFF = flag_OFF,
	       flag_PTAUTON  = flag_ON,
	       flag_PTAUTMAX
} FLAG_PTAUTTYPE;

/* State definitions for flag_PUNC */
typedef enum { flag_PUNCMIN = -1,
	       flag_PUNCOFF = flag_OFF,
	       flag_PUNCON  = flag_ON,
	       flag_PUNCMAX
} FLAG_PUNCTYPE;

/* State definitions for flag_RBMRR */
typedef enum { flag_RBMRRMIN = -1,
               flag_RBMRROFF = flag_OFF,
               flag_RBMRRON  = flag_ON,
               flag_RBMRRMAX
} FLAG_RBMRRTYPE;

/* State definitions for flag_RBREW */
typedef enum { flag_RBREWMIN = -1,
               flag_RBREWOFF = flag_OFF,
               flag_RBREWON  = flag_ON,
               flag_RBREWMAX
} FLAG_RBREWTYPE;

/* State definitions for flag_RBCRW */
typedef enum { flag_RBCRWMIN = -1,
               flag_RBCRWOFF = flag_OFF,
               flag_RBCRWON  = flag_ON,
               flag_RBCRWMAX
} FLAG_RBCRWTYPE;

/* State definitions for flag_RBSUB */
typedef enum { flag_RBSUBMIN = -1,
               flag_RBSUBOFF = flag_OFF,
               flag_RBSUBON  = flag_ON,
               flag_RBSUBMAX
} FLAG_RBSUBTYPE;

/* State definitions for flag_RCON */
typedef enum { flag_RCONMIN = -1,
               flag_RCONOFF = flag_OFF,
               flag_RCONON  = flag_ON,
               flag_RCONMAX
} FLAG_RCONTYPE;

/* State definitions for flag_RFMRR */
typedef enum { flag_RFMRRMIN = -1,
               flag_RFMRROFF = flag_OFF,
               flag_RFMRRON  = flag_ON,
               flag_RFMRRMAX
} FLAG_RFMRRTYPE;

/* State definitions for flag_RFREW */
typedef enum { flag_RFREWMIN = -1,
               flag_RFREWOFF = flag_OFF,
               flag_RFREWON  = flag_ON,
               flag_RFREWMAX
} FLAG_RFREWTYPE;

/* State definitions for flag_RFCRW */
typedef enum { flag_RFCRWMIN = -1,
               flag_RFCRWOFF = flag_OFF,
               flag_RFCRWON  = flag_ON,
               flag_RFCRWMAX
} FLAG_RFCRWTYPE;

/* State definitions for flag_RFSUB */
typedef enum { flag_RFSUBMIN = -1,
               flag_RFSUBOFF = flag_OFF,
               flag_RFSUBON  = flag_ON,
               flag_RFSUBMAX
} FLAG_RFSUBTYPE;

/* State definitions for flag_RINPUT */
typedef enum { flag_RINPUTMIN = -1,
               flag_RINPUTOFF = flag_OFF,
               flag_RINPUTON  = flag_ON,
               flag_RINPUTMAX
} FLAG_RINPUTTYPE;

/* State definitions for flag_ROBV */
typedef enum { flag_ROBVMIN = -1,
               flag_ROBVOFF = flag_OFF,
               flag_ROBVON  = flag_ON,
               flag_ROBVMAX
} FLAG_ROBVTYPE;

/* State definitions for flag_RAED */
typedef enum { flag_RAEDMIN = -1,
	       flag_RAEDOFF = flag_OFF,
	       flag_RAEDSOUND,
	       flag_RAEDPOTUNSOUND,
	       flag_RAEDMAX
} FLAG_RAEDTYPE;

/* State definitions for flag_RSSI */
typedef enum { flag_RSSIMIN = -1,
               flag_RSSIOFF = flag_OFF,
               flag_RSSION  = flag_ON,
               flag_RSSIMAX
} FLAG_RSSITYPE;

/* State definitions for flag_RSST */
typedef enum { flag_RSSTMIN = -1,
               flag_RSSTOFF = flag_OFF,
               flag_RSSTON  = flag_ON,
               flag_RSSTMAX
} FLAG_RSSTTYPE;

/* State definitions for flag_RTAUT */
typedef enum { flag_RTAUTMIN = -1,
	       flag_RTAUTOFF = flag_OFF,
	       flag_RTAUTSYNTACTIC,
	       flag_RTAUTSEMANTIC,
	       flag_RTAUTMAX
} FLAG_RTAUTTYPE;

/* State definitions for flag_RTER */
typedef enum { flag_RTERMIN = -1,
	       flag_RTEROFF = flag_OFF,
	       flag_RTERMAX = INT_MAX
} FLAG_RTERTYPE;

/* State definitions for flag_RUNC */
typedef enum { flag_RUNCMIN = -1,
               flag_RUNCOFF = flag_OFF,
               flag_RUNCON  = flag_ON,
               flag_RUNCMAX
} FLAG_RUNCTYPE;

/* State definitions for flag_SATINPUT */
typedef enum { flag_SATINPUTMIN = -1,
               flag_SATINPUTOFF = flag_OFF,
               flag_SATINPUTON  = flag_ON,
               flag_SATINPUTMAX
} FLAG_SATINPUTTYPE;

/* State definitions for flag_SELECT */
typedef enum { flag_SELECTMIN = -1,
	       flag_SELECTOFF = flag_OFF,
	       flag_SELECTIFSEVERALMAXIMAL,
	       flag_SELECTALWAYS,
	       flag_SELECTMAX
} FLAG_SELECTTYPE;

/* State definitions for flag_SORTS */
typedef enum { flag_SORTSMIN = -1,
	       flag_SORTSOFF = flag_OFF,
	       flag_SORTSMONADICWITHVARIABLE,
	       flag_SORTSMONADICALL,
	       flag_SORTSMAX
} FLAG_SORTSTYPE;

/* State definitions for flag_SOS */
typedef enum { flag_SOSMIN = -1,
	       flag_SOSOFF = flag_OFF,
	       flag_SOSON  = flag_ON,
	       flag_SOSMAX
} FLAG_SOSTYPE;

/* State definitions for flag_SPLITS */
typedef enum { flag_SPLITSMIN = -2,
	       flag_SPLITSUNLIMITED,
	       flag_SPLITSOFF = flag_OFF,
	       flag_SPLITSMAX = INT_MAX
} FLAG_SPLITSTYPE;

/* State definitions for flag_STDIN */
typedef enum { flag_STDINMIN = -1,
	       flag_STDINOFF = flag_OFF,
	       flag_STDINON  = flag_ON,
	       flag_STDINMAX
} FLAG_STDINTYPE;

/* State definitions for flag_TDFG2OTTEROPTIONS */
typedef enum { flag_TDFG2OTTEROPTIONSMIN = -1,
	       flag_TDFG2OTTEROPTIONSOFF = flag_OFF,
	       flag_TDFG2OTTEROPTIONSPROOFCHECK,
	       flag_TDFG2OTTEROPTIONSAUTO,
	       flag_TDFG2OTTEROPTIONSAUTO2,
	       flag_TDFG2OTTEROPTIONSMAX
} FLAG_TDFG2OTTEROPTIONSTYPE;

/* State definitions for flag_TIMELIMIT */
typedef enum { flag_TIMELIMITMIN = -2,
	       flag_TIMELIMITUNLIMITED,
	       flag_TIMELIMITMAX = INT_MAX
} FLAG_TIMELIMITTYPE;

/* State definitions for flag_VARWEIGHT */
typedef enum { flag_VARWEIGHTMIN = 0,
	       flag_VARWEIGHTMAX = INT_MAX
} FLAG_VARWEIGHTTYPE;

/* State definitions for flag_WDRATIO */
typedef enum { flag_WDRATIOMIN = 0,
	       flag_WDRATIOMAX = INT_MAX
} FLAG_WDRATIOTYPE;


/* Define all flags */

typedef enum { flag_AUTO, flag_STDIN, flag_INTERACTIVE, flag_FLOTTER,
	       flag_SOS,

               flag_SPLITS,     flag_MEMORY,     flag_TIMELIMIT,
	       flag_DOCSST,     flag_DOCPROOF,
	       flag_DOCSPLIT,   flag_LOOPS,      flag_PSUB,
	       flag_PREW,       flag_PCRW,       flag_PCON,
	       flag_PTAUT,      flag_POBV,       flag_PSSI,
	       flag_PSST,       flag_PMRR,       flag_PUNC,
	       flag_PAED,

	       flag_PDER,       flag_PGIVEN,     flag_PLABELS,
	       flag_PKEPT,      flag_PPROBLEM,   flag_PEMPTYCLAUSE,
	       flag_PSTATISTIC, flag_FPMODEL,    flag_FPDFGPROOF,
	       flag_PFLAGS,     flag_POPTSKOLEM, flag_PSTRSKOLEM,
	       flag_PBDC,       flag_PBINC,
	       flag_PAPPLYDEFS,

	       flag_SELECT,     flag_RINPUT,     flag_SORTS,
	       flag_SATINPUT,   flag_WDRATIO,    flag_PREFCON,
	       flag_FULLRED,
	       flag_FUNCWEIGHT, flag_VARWEIGHT,  flag_PREFVAR,
	       flag_BOUNDMODE,  flag_BOUNDSTART, 
	       flag_BOUNDLOOPS, flag_APPLYDEFS,

	       flag_ORD,

	       flag_CNFOPTSKOLEM, flag_CNFSTRSKOLEM, flag_CNFPROOFSTEPS,
	       flag_CNFRENAMING,  flag_CNFPRENAMING, flag_CNFFEQREDUCTIONS,
	       
	       flag_IEMS,       flag_ISOR,
	       flag_IEQR,       flag_IERR,
	       flag_IEQF,       flag_IMPM,       flag_ISPR,
	       flag_IOPM,       flag_ISPM,
	       flag_ISPL,       flag_IORE,       flag_ISRE,
	       flag_ISHY,       flag_IOHY,       flag_IURR,
	       flag_IOFC,       flag_ISFC,
	       flag_IUNR,       flag_IBUR,       flag_IDEF,

	       flag_RFREW,      flag_RBREW,
	       flag_RFCRW,      flag_RBCRW,
	       flag_RFMRR,      flag_RBMRR,
	       flag_ROBV,       flag_RUNC,       flag_RTER,
	       flag_RTAUT,      flag_RSST,       flag_RSSI,
	       flag_RFSUB,      flag_RBSUB,      flag_RAED,
	       flag_RCON,       
	       
	       flag_TDFG2OTTEROPTIONS,

	       flag_MAXFLAG } FLAG_ID;     /* flag_MAXFLAG is a final Dummy */


/* Define different flag types */
typedef enum { flag_INFERENCE,
	       flag_PRINTING,
	       flag_REDUCTION,
	       flag_UNIQUE,               /* miscellaneous flags */
	       flag_MAXTYPE
} FLAG_TYPE;


/* Define the flag data type */
typedef int FLAG;

/* Define the internal representation of a flag store */
typedef FLAG FLAGARRAY[flag_MAXFLAG];

/* Define the flag store */
typedef FLAG *FLAGSTORE;

/**************************************************************/
/* Functions                                                  */
/**************************************************************/

void        flag_Init(void);
void        flag_InitFlotterFlags(FLAGSTORE, FLAGSTORE);
void        flag_InitFlotterSubproofFlags(FLAGSTORE, FLAGSTORE);
FLAGSTORE   flag_DefaultStore(void);
void        flag_Print(FLAGSTORE);
void        flag_FPrint(FILE*, FLAGSTORE);
BOOL        flag_Lookup(const char*);
FLAG_ID     flag_Id(const char*);
const char* flag_Name(FLAG_ID);
int         flag_Minimum(FLAG_ID);
int         flag_Maximum(FLAG_ID);
FLAG_TYPE   flag_Type(FLAG_ID Flag);
void        flag_ClearInferenceRules(FLAGSTORE Store);
void        flag_ClearReductionRules(FLAGSTORE Store);
void        flag_ClearPrinting(FLAGSTORE Store);
void        flag_SetReductionsToDefaults(FLAGSTORE Store);
void        flag_CheckStore(FLAGSTORE Store);

/**************************************************************/
/* Macros                                                     */
/**************************************************************/

static __inline__ void flag_CheckFlagIdInRange(FLAG_ID FlagId)
  /* prints an error report if a FLAG_ID is not valid */
{
#ifdef CHECK
  if (FlagId >= flag_MAXFLAG) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In flag_CheckFlagIdInRange: Range of flags exceeded.");
    misc_FinishErrorReport();
  }
#endif
}

static __inline__ void flag_CheckFlagValueInRange(FLAG_ID FlagId, int Value)
  /* prints an error report if a flag's value is out of range */
{
  flag_CheckFlagIdInRange(FlagId);
 
  if (Value <= flag_Minimum(FlagId)) {
     misc_StartUserErrorReport();
     misc_UserErrorReport("\n Error: Flag value %d is too small for flag %s.\n", Value, flag_Name(FlagId));
     misc_FinishUserErrorReport();
  }
  else
    if (Value >= flag_Maximum(FlagId)) {
      misc_StartUserErrorReport();
      misc_UserErrorReport("\n Error: Flag value %d is too large for flag %s.\n", Value, flag_Name(FlagId));
      misc_FinishUserErrorReport();
    }
}

static __inline__ void flag_CheckFlagTypeInRange(FLAG_TYPE Type)
  /* prints an error report if a flag's type is out of range */
{
#ifdef CHECK
  if (Type >= flag_MAXTYPE) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In flag_CheckFlagTypeInRange: Range of types exceeded.");
    misc_FinishErrorReport();
  }
#endif
}

static __inline__ BOOL flag_StoreIsDefaultStore(FLAGSTORE Store)
     /* returns TRUE if a flag store is the default store, FALSE otherwise */
{
  return (BOOL) (Store == flag_DefaultStore());
}

static __inline__ int flag_GetFlagValue(FLAGSTORE Store, FLAG_ID FlagId)
{
  int Value;

  flag_CheckFlagIdInRange(FlagId);

  Value = Store[FlagId];
#ifdef CHECK
  if (Value == flag_CLEAN) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In flag_GetFlagValue:");
    misc_ErrorReport(" Attempt to read undefined flag value.");
    misc_FinishErrorReport();
  }
#endif

  return Value;
}

static __inline__ void flag_SetFlagValue(FLAGSTORE Store, FLAG_ID FlagId, int Value)
{
#ifdef CHECK
  if (flag_StoreIsDefaultStore(Store)) {
    misc_StartErrorReport();
    misc_ErrorReport("\n In flag_SetFlagValue:");
    misc_ErrorReport(" Attempt to modify default flag value.");
    misc_FinishErrorReport();
  }
#endif

  flag_CheckFlagIdInRange(FlagId);

  flag_CheckFlagValueInRange (FlagId, Value);

  Store[FlagId] = Value;
}

static __inline__ BOOL flag_ValueIsClean(FLAGSTORE Store, FLAG_ID FlagId)
{
#ifdef CHECK
  flag_CheckFlagIdInRange(FlagId);
  return (BOOL) (Store[FlagId] == flag_CLEAN);
#else
  return (BOOL) (flag_GetFlagValue(Store, FlagId) == flag_CLEAN);
#endif
}

static __inline__ void flag_CleanStore(FLAGSTORE Store)
{
  int i;
  for (i = 0; i < flag_MAXFLAG; i++)
    Store[i] = flag_CLEAN;  
}


static __inline__ FLAGSTORE flag_CreateStore(void)
     /* creates a fresh, clean FLAGSTORE */
{
  FLAGSTORE store;

  store = (FLAGSTORE) memory_Malloc(sizeof(FLAGARRAY));
  flag_CleanStore(store);
  return store;
}


static __inline__ void flag_DeleteStore(FLAGSTORE Store)
{
#ifdef CHECK
  /* Check if the flag store is a valid state */
  flag_CheckStore(Store);
#endif

  memory_Free(Store,sizeof(FLAGARRAY));
}


static __inline__ void flag_InitStoreByDefaults(FLAGSTORE Store)
{
  FLAG_ID i;
  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i++)
    flag_SetFlagValue(Store, i, flag_GetFlagValue(flag_DefaultStore(),i));  
}


static __inline__ void flag_SetFlagToDefault(FLAGSTORE Store, FLAG_ID Flag)
{
  flag_SetFlagValue(Store, Flag, flag_GetFlagValue(flag_DefaultStore(), Flag));
}


static __inline__ void flag_TransferFlag(FLAGSTORE Source, FLAGSTORE Destination, FLAG_ID FlagId)
{
  flag_SetFlagValue(Destination, FlagId, flag_GetFlagValue(Source, FlagId));
}


static __inline__ void flag_TransferAllFlags(FLAGSTORE Source, FLAGSTORE Destination)
{
  FLAG_ID i;
  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i++)
    Destination[i] = Source[i];
}


static __inline__ void flag_TransferSetFlags(FLAGSTORE Source, FLAGSTORE Destination)
{
  FLAG_ID i;
  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i++)
    if (!flag_ValueIsClean(Source,i))
      flag_TransferFlag(Source, Destination, i);
}


static __inline__ BOOL flag_IsOfType(FLAG_ID Flag, FLAG_TYPE Type)
/**************************************************************
  INPUT:   A FlagId and a flag type.
  RETURNS: TRUE is the flag is of given type,
           FALSE otherwise.
***************************************************************/
{
  flag_CheckFlagIdInRange(Flag);
  flag_CheckFlagTypeInRange(Type);

  return (BOOL) (flag_Type(Flag) == Type);
}


static __inline__ BOOL flag_IsInference(FLAG_ID Flag) 
/**************************************************************
  INPUT:   A FlagId.
  RETURNS: TRUE is the flag is an inference flag,
           FALSE otherwise.
***************************************************************/
{
  flag_CheckFlagIdInRange(Flag);

  return flag_IsOfType(Flag, flag_INFERENCE);
}


static __inline__ BOOL flag_IsReduction(FLAG_ID Flag) 
/**************************************************************
  INPUT:   A FlagId.
  RETURNS: TRUE is the flag is a reduction flag,
           FALSE otherwise.
***************************************************************/
{
  flag_CheckFlagIdInRange(Flag);

  return flag_IsOfType(Flag, flag_REDUCTION);
}


static __inline__ BOOL flag_IsPrinting(FLAG_ID Flag) 
/**************************************************************
  INPUT:   A FlagId.
  RETURNS: TRUE is the flag is a printing flag,
           FALSE otherwise.
***************************************************************/
{
  flag_CheckFlagIdInRange(Flag);

  return flag_IsOfType(Flag, flag_PRINTING);
}


static __inline__ BOOL flag_IsUnique(FLAG_ID Flag) 
/**************************************************************
  INPUT:   A FlagId.
  RETURNS: TRUE is the flag is an unique flag,
           FALSE otherwise.
***************************************************************/
{
  flag_CheckFlagIdInRange(Flag);

  return flag_IsOfType(Flag, flag_UNIQUE);
}


static __inline__ void flag_PrintReductionRules(FLAGSTORE Store)
/**************************************************************
  INPUT:   A FlagStore.
  RETURNS: Nothing.
  EFFECT:  Prints the values of all reduction flags to stdout.
***************************************************************/
{
  FLAG_ID i;
  fputs("\n Reductions: ", stdout);

  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i++) {
    if (flag_IsReduction(i) && flag_GetFlagValue(Store, i))
      printf("%s=%d ",flag_Name(i), flag_GetFlagValue(Store, i));
  }
}

static __inline__ void flag_PrintInferenceRules(FLAGSTORE Store)
/**************************************************************
  INPUT:   A FlagStore.
  RETURNS: Nothing.
  EFFECT:  Prints the values of all inference flags to stdout.
***************************************************************/
{
  FLAG_ID i;
  fputs("\n Inferences: ", stdout);

  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i++) {
    if (flag_IsInference(i) && flag_GetFlagValue(Store, i))
      printf("%s=%d ",flag_Name(i), flag_GetFlagValue(Store,i));
  }
}

#endif






