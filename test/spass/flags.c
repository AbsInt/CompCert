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
/* $Revision: 35442 $                                        * */
/* $State$                                            * */
/* $Date: 2007-03-28 17:24:40 -0700 (Wed, 28 Mar 2007) $                             * */
/* $Author: jeffc $                                       * */
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

#include <stdio.h>
#include <string.h>

#include "flags.h"
#include "misc.h"
#include "stringsx.h"

/**************************************************************/
/* Global Declarations                                        */
/**************************************************************/

const int flag_CLEAN = -5;


/**************************************************************/
/* File Local Declarations                                    */
/**************************************************************/

/* Define flag properties */
typedef struct {
  int        minimum;
  int        maximum;
  FLAG_TYPE  type;
  const char *name;
} FLAG_PROPERTY;


static FLAGARRAY     flag_DEFAULTSTORE;
static FLAG_PROPERTY flag_PROPERTIES[flag_MAXFLAG];


/**************************************************************/
/* Functions                                                  */
/**************************************************************/

static __inline__ void flag_InitIntern (FLAG_ID Flag, FLAG_TYPE Type,
					const char *Name, int Value,
					int Minimum, int Maximum)
{
  FLAG_PROPERTY *property;

  flag_CheckFlagIdInRange(Flag);

  property = &(flag_PROPERTIES[Flag]);

  /* Set the flag type */
  flag_CheckFlagTypeInRange(Type);
  property->type = Type;

  /* Set flag name */
  property->name = Name;

  /* Set flag minimum and maximum */
  property->minimum = Minimum;
  property->maximum = Maximum;

  /* Set flag value */
#ifdef CHECK
  if (Value > Minimum && Value < Maximum) {
#endif

    flag_DEFAULTSTORE[Flag] = Value;

#ifdef CHECK
  }
  else {
    misc_StartErrorReport();
    misc_ErrorReport("\n In flag_InitIntern: Default value out of range.");
    misc_ErrorReport("\n Flag: %s. Value: %d.", Name, Value);
    misc_FinishErrorReport();
  }
#endif
}

void flag_Init(void)
/**************************************************************
  INPUT:   None.
  RETURNS: Nothing.
  EFFECT:  Sets all default values for known flags.
  MEMORY:  Allocates memory for the default store.
***************************************************************/
{
  /* Autonomous mode */
  flag_InitIntern(flag_AUTO, flag_UNIQUE, "Auto", flag_AUTOON,
		  flag_AUTOMIN, flag_AUTOMAX);

  /* Set of Support Mode */
  flag_InitIntern(flag_SOS, flag_UNIQUE, "SOS", flag_SOSOFF,
		  flag_SOSMIN, flag_SOSMAX);

  /* If set input is considered from stdin and printed to stdout */
  flag_InitIntern(flag_STDIN, flag_UNIQUE, "Stdin", flag_STDINOFF,
		  flag_STDINMIN, flag_STDINMAX);

   /* If set interactive queries are possible */
  flag_InitIntern(flag_INTERACTIVE, flag_UNIQUE, "Interactive", flag_INTERACTIVEOFF,
		  flag_INTERACTIVEMIN, flag_INTERACTIVEMAX);

  /* If set only Flotter CNF-translation is performed */
  flag_InitIntern(flag_FLOTTER, flag_UNIQUE, "Flotter", flag_FLOTTEROFF,
		  flag_FLOTTERMIN, flag_FLOTTERMAX);

  /* Allowed number of loops, -1 means no restriction */
  flag_InitIntern(flag_LOOPS, flag_UNIQUE, "Loops", flag_LOOPSUNLIMITED,
		  flag_LOOPSMIN, flag_LOOPSMAX);

  /* Allowed number of splits, -1 means no restriction */
  flag_InitIntern(flag_SPLITS, flag_UNIQUE, "Splits", flag_SPLITSOFF,
		  flag_SPLITSMIN, flag_SPLITSMAX);

  /* Decides the level of sort usage: if 0 then no sort information is processed,
     if 1 all negative monadic literals with a variable as its argument are processed,
     if 2 all negative monadic literals are processed */
  flag_InitIntern(flag_SORTS, flag_UNIQUE, "Sorts", flag_SORTSOFF,
		  flag_SORTSMIN, flag_SORTSMAX);

  /* ForwardSubsumption output not activated */
  flag_InitIntern(flag_PSUB, flag_PRINTING, "PSub", flag_PSUBOFF,
		  flag_PSUBMIN, flag_PSUBMAX);

  /* Maximal memory allocation */
  flag_InitIntern(flag_MEMORY, flag_UNIQUE, "Memory", flag_MEMORYUNLIMITED,
		  flag_MEMORYMIN, flag_MEMORYMAX);

  /* Document static soft typing  */
  flag_InitIntern(flag_DOCSST, flag_PRINTING, "DocSST", flag_DOCSSTOFF,
		  flag_DOCSSTMIN, flag_DOCSSTMAX);

  /* Rewriting output not activated  */
  flag_InitIntern(flag_PREW, flag_PRINTING, "PRew", flag_PREWOFF,
		  flag_PREWMIN, flag_PREWMAX);

  /* Contextual rewriting output not activated  */
  flag_InitIntern(flag_PCRW, flag_PRINTING, "PCRw", flag_PCRWOFF,
		  flag_PCRWMIN, flag_PCRWMAX);

  /* Condensing output not activated  */
  flag_InitIntern(flag_PCON, flag_PRINTING, "PCon", flag_PCONOFF,
		  flag_PCONMIN, flag_PCONMAX);

 /* Assignment Equation Deletion output not activated  */
  flag_InitIntern(flag_PAED, flag_PRINTING, "PAED", flag_PAEDOFF,
		  flag_PAEDMIN, flag_PAEDMAX);

  /* Tautology output not activated  */
  flag_InitIntern(flag_PTAUT, flag_PRINTING, "PTaut", flag_PTAUTOFF,
		  flag_PTAUTMIN, flag_PTAUTMAX);

  /* Output of obvious red. not activated  */
  flag_InitIntern(flag_POBV, flag_PRINTING, "PObv", flag_POBVOFF,
		  flag_POBVMIN, flag_POBVMAX);

  /* SortSimplification output not activated  */
  flag_InitIntern(flag_PSSI, flag_PRINTING, "PSSi", flag_PSSIOFF,
		  flag_PSSIMIN, flag_PSSIMAX);

  /* Static soft typing output not activated  */
  flag_InitIntern(flag_PSST, flag_PRINTING, "PSST", flag_PSSTOFF,
		  flag_PSSTMIN, flag_PSSTMAX);

  /* Proof output not activated  */
  flag_InitIntern(flag_DOCPROOF, flag_UNIQUE, "DocProof", flag_DOCPROOFOFF,
		  flag_DOCPROOFMIN, flag_DOCPROOFMAX);

  /* Matching Replacement Resolution output not activated  */
  flag_InitIntern(flag_PMRR, flag_PRINTING, "PMRR", flag_PMRROFF,
		  flag_PMRRMIN, flag_PMRRMAX);

  /* Unit conflict output not activated  */
  flag_InitIntern(flag_PUNC, flag_PRINTING, "PUnC", flag_PUNCOFF,
		  flag_PUNCMIN, flag_PUNCMAX);

  /* Derived clauses output not activated  */
  flag_InitIntern(flag_PDER, flag_PRINTING, "PDer", flag_PDEROFF,
		  flag_PDERMIN, flag_PDERMAX);

  /* Given clause output activated  */
  flag_InitIntern(flag_PGIVEN, flag_PRINTING, "PGiven", flag_PGIVENON,
		  flag_PGIVENMIN, flag_PGIVENMAX);

  /* If labels are created they are not printed  */
  flag_InitIntern(flag_PLABELS, flag_PRINTING, "PLabels", flag_PLABELSOFF,
		  flag_PLABELSMIN, flag_PLABELSMAX);

  /* Kept clauses output not activated  */
  flag_InitIntern(flag_PKEPT, flag_PRINTING, "PKept", flag_PKEPTOFF,
		  flag_PKEPTMIN, flag_PKEPTMAX);

  /* Split backtrack emphasizing not activated */
  flag_InitIntern(flag_DOCSPLIT, flag_PRINTING, "DocSplit", flag_DOCSPLITOFF,
		  flag_DOCSPLITMIN, flag_DOCSPLITMAX);

  /* Print information about input clauses */
  flag_InitIntern(flag_PPROBLEM, flag_PRINTING, "PProblem", flag_PPROBLEMON,
		  flag_PPROBLEMMIN, flag_PPROBLEMMAX);

  /* Print all derived empty clauses */
  flag_InitIntern(flag_PEMPTYCLAUSE, flag_PRINTING, "PEmptyClause", flag_PEMPTYCLAUSEOFF,
		  flag_PEMPTYCLAUSEMIN, flag_PEMPTYCLAUSEMAX);

  /* Print statistic about memory, clauses */
  flag_InitIntern(flag_PSTATISTIC, flag_PRINTING, "PStatistic", flag_PSTATISTICON,
		  flag_PSTATISTICMIN, flag_PSTATISTICMAX);

  /* Output saturated set of clauses to file, default no */
  flag_InitIntern(flag_FPMODEL, flag_PRINTING, "FPModel", flag_FPMODELOFF,
		  flag_FPMODELMIN, flag_FPMODELMAX);

  /* Output proof in DFG format to file, default no */
  flag_InitIntern(flag_FPDFGPROOF, flag_PRINTING, "FPDFGProof", flag_FPDFGPROOFOFF,
		  flag_FPDFGPROOFMIN, flag_FPDFGPROOFMAX);

  /* Output the actual values of all SPASS flags */
  flag_InitIntern(flag_PFLAGS, flag_PRINTING, "PFlags", flag_PFLAGSOFF,
		  flag_PFLAGSMIN, flag_PFLAGSMAX);

  /* Optimized skolemization output not activated  */
  flag_InitIntern(flag_POPTSKOLEM, flag_PRINTING, "POptSkolem", flag_POPTSKOLEMOFF,
		  flag_POPTSKOLEMMIN, flag_POPTSKOLEMMAX);

  /* Strong skolemization output not activated  */
  flag_InitIntern(flag_PSTRSKOLEM, flag_PRINTING, "PStrSkolem", flag_PSTRSKOLEMOFF,
		  flag_PSTRSKOLEMMIN, flag_PSTRSKOLEMMAX);

  /* Printing of clauses deleted by bound restriction not activated  */
  flag_InitIntern(flag_PBDC, flag_PRINTING, "PBDC", flag_PBDCOFF,
		  flag_PBDCMIN, flag_PBDCMAX);

  /* Printing of bound increase actions  */
  flag_InitIntern(flag_PBINC, flag_PRINTING, "PBInc", flag_PBINCOFF,
		  flag_PBINCMIN, flag_PBINCMAX);

  /* Application of definitions  output activated  */
  flag_InitIntern(flag_PAPPLYDEFS, flag_PRINTING, "PApplyDefs", flag_PAPPLYDEFSOFF,
		  flag_PAPPLYDEFSMIN, flag_PAPPLYDEFSMAX);

  /* Amount of time (seconds) available to SPASS, -1 means arbitrary */
  flag_InitIntern(flag_TIMELIMIT, flag_UNIQUE, "TimeLimit", flag_TIMELIMITUNLIMITED,
		  flag_TIMELIMITMIN, flag_TIMELIMITMAX);
  
  /* Select: 0 -> no selection, 1 -> select if multiple maximal literals, 2 -> always select */
  flag_InitIntern(flag_SELECT, flag_UNIQUE, "Select", flag_SELECTIFSEVERALMAXIMAL,
		  flag_SELECTMIN, flag_SELECTMAX);

  /* Activates the inference rule Empty Sort */
  flag_InitIntern(flag_IEMS, flag_INFERENCE, "IEmS", flag_EMPTYSORTOFF,
		  flag_EMPTYSORTMIN, flag_EMPTYSORTMAX);

  /* Activates the inference rule Sort Resolution */
  flag_InitIntern(flag_ISOR, flag_INFERENCE, "ISoR", flag_SORTRESOLUTIONOFF,
		  flag_SORTRESOLUTIONMIN, flag_SORTRESOLUTIONMAX);

  /* Activates the inference rule Equality Resolution */
  flag_InitIntern(flag_IEQR, flag_INFERENCE, "IEqR", flag_EQUALITYRESOLUTIONOFF,
		  flag_EQUALITYRESOLUTIONMIN, flag_EQUALITYRESOLUTIONMAX);

  /* Activates the inference rule Reflexivity Resolution */
  flag_InitIntern(flag_IERR, flag_INFERENCE, "IERR", flag_REFLEXIVITYRESOLUTIONOFF,
		  flag_REFLEXIVITYRESOLUTIONMIN, flag_REFLEXIVITYRESOLUTIONMAX);

  /* Activates the inference rule Equality Factoring */
  flag_InitIntern(flag_IEQF, flag_INFERENCE, "IEqF", flag_EQUALITYFACTORINGOFF,
		  flag_EQUALITYFACTORINGMIN, flag_EQUALITYFACTORINGMAX);

  /* Activates the inference rule Merging Paramodulation */
  flag_InitIntern(flag_IMPM, flag_INFERENCE, "IMPm", flag_MERGINGPARAMODULATIONOFF,
		  flag_MERGINGPARAMODULATIONMIN, flag_MERGINGPARAMODULATIONMAX);

  /* Activates the inference rule Superposition Right */
  flag_InitIntern(flag_ISPR, flag_INFERENCE, "ISpR", flag_SUPERPOSITIONRIGHTOFF,
		  flag_SUPERPOSITIONRIGHTMIN, flag_SUPERPOSITIONRIGHTMAX);
  
  /* Inference rule Ordered Paramodulation not active */  
  flag_InitIntern(flag_IOPM, flag_INFERENCE, "IOPm", flag_ORDEREDPARAMODULATIONOFF,
		  flag_ORDEREDPARAMODULATIONMIN, flag_ORDEREDPARAMODULATIONMAX);

  /*   Inference rule Paramodulation not active */  
  flag_InitIntern(flag_ISPM, flag_INFERENCE, "ISPm", flag_STANDARDPARAMODULATIONOFF,
		  flag_STANDARDPARAMODULATIONMIN, flag_STANDARDPARAMODULATIONMAX);   

  /* Activates the inference rule Superposition Left */
  flag_InitIntern(flag_ISPL, flag_INFERENCE, "ISpL", flag_SUPERPOSITIONLEFTOFF,
		  flag_SUPERPOSITIONLEFTMIN, flag_SUPERPOSITIONLEFTMAX);
  
  /* Activates the inference rule Ordered Resolution */
  flag_InitIntern(flag_IORE, flag_INFERENCE, "IORe", flag_ORDEREDRESOLUTIONOFF,
		  flag_ORDEREDRESOLUTIONMIN, flag_ORDEREDRESOLUTIONMAX);

  /* Activates the inference rule Standard Resolution */
  flag_InitIntern(flag_ISRE, flag_INFERENCE, "ISRe", flag_STANDARDRESOLUTIONOFF,
		  flag_STANDARDRESOLUTIONMIN, flag_STANDARDRESOLUTIONMAX);

  /* Activates the inference rule Standard Hyperresolution */
  flag_InitIntern(flag_ISHY, flag_INFERENCE, "ISHy", flag_STANDARDHYPERRESOLUTIONOFF,
		  flag_STANDARDHYPERRESOLUTIONMIN, flag_STANDARDHYPERRESOLUTIONMAX);
  
  /* Activates the inference rule Ordered Hyperresolution */
  flag_InitIntern(flag_IOHY, flag_INFERENCE, "IOHy", flag_ORDEREDHYPERRESOLUTIONOFF,
		  flag_ORDEREDHYPERRESOLUTIONMIN, flag_ORDEREDHYPERRESOLUTIONMAX);

  /* Activates the inference rule UR Resolution */
  flag_InitIntern(flag_IURR, flag_INFERENCE, "IURR", flag_UNITRESULTINGRESOLUTIONOFF,
		  flag_UNITRESULTINGRESOLUTIONMIN, flag_UNITRESULTINGRESOLUTIONMAX);

  /* Activates the inference rule Ordered Factoring */
  flag_InitIntern(flag_IOFC, flag_INFERENCE, "IOFc", flag_FACTORINGOFF,
		  flag_FACTORINGMIN, flag_FACTORINGMAX);

    /* Activates the inference rule Standard Factoring */
  flag_InitIntern(flag_ISFC, flag_INFERENCE, "ISFc", flag_STANDARDFACTORINGOFF,
		  flag_STANDARDFACTORINGMIN, flag_STANDARDFACTORINGMAX);

  /* Activates the inference rule Bounded Unit Resolution */
  flag_InitIntern(flag_IBUR, flag_INFERENCE, "IBUR", flag_BOUNDEDDEPTHUNITRESOLUTIONOFF,
		  flag_BOUNDEDDEPTHUNITRESOLUTIONMIN, flag_BOUNDEDDEPTHUNITRESOLUTIONMAX);

  /* Activates the inference rule Definition Application */
  flag_InitIntern(flag_IDEF, flag_INFERENCE, "IDEF", flag_DEFINITIONAPPLICATIONOFF,
		  flag_DEFINITIONAPPLICATIONMIN, flag_DEFINITIONAPPLICATIONMAX);

  /* Activates the inference rule  Unit Resolution */
  flag_InitIntern(flag_IUNR, flag_INFERENCE, "IUnR", flag_UNITRESOLUTIONOFF,
		  flag_UNITRESOLUTIONMIN, flag_UNITRESOLUTIONMAX);
  
  /* Activates Forward Rewriting */
  flag_InitIntern(flag_RFREW, flag_REDUCTION, "RFRew", flag_RFREWOFF,
		  flag_RFREWMIN, flag_RFREWMAX);

  /* Activates Backward Rewriting */
  flag_InitIntern(flag_RBREW, flag_REDUCTION, "RBRew", flag_RBREWOFF,
		  flag_RBREWMIN, flag_RBREWMAX);

  /* Activates Forward Contextual Rewriting */
  flag_InitIntern(flag_RFCRW, flag_REDUCTION, "RFCRw", flag_RFCRWOFF,
		  flag_RFCRWMIN, flag_RFCRWMAX);

  /* Activates Backward Contextual Rewriting */
  flag_InitIntern(flag_RBCRW, flag_REDUCTION, "RBCRw", flag_RBCRWOFF,
		  flag_RBCRWMIN, flag_RBCRWMAX);

  /* Activates Unit Conflict */
  flag_InitIntern(flag_RUNC, flag_REDUCTION, "RUnC", flag_RUNCOFF,
		  flag_RUNCMIN, flag_RUNCMAX);

  /* Activates Terminator */
  flag_InitIntern(flag_RTER, flag_REDUCTION, "RTer", flag_RTEROFF,
		  flag_RTERMIN, flag_RTERMAX);

  /* Activates Forward Subsumption */
  flag_InitIntern(flag_RFSUB, flag_REDUCTION, "RFSub", flag_RFSUBOFF,
		  flag_RFSUBMIN, flag_RFSUBMAX);

  /* Activates Backward Subsumption */
  flag_InitIntern(flag_RBSUB, flag_REDUCTION, "RBSub", flag_RBSUBOFF,
		  flag_RBSUBMIN, flag_RBSUBMAX);

  /* Activates Forward Matching Replacement Resolution */
  flag_InitIntern(flag_RFMRR, flag_REDUCTION, "RFMRR", flag_RFMRROFF,
		  flag_RFMRRMIN, flag_RFMRRMAX);

  /* Activates Backward Matching Replacement Resolution */
  flag_InitIntern(flag_RBMRR, flag_REDUCTION, "RBMRR", flag_RBMRROFF,
		  flag_RBMRRMIN, flag_RBMRRMAX);

  /* Activates the reduction rule Obvious Reduction */
  flag_InitIntern(flag_ROBV, flag_REDUCTION, "RObv", flag_ROBVOFF,
		  flag_ROBVMIN, flag_ROBVMAX);

  /* Activates the reduction rule Tautology */
  flag_InitIntern(flag_RTAUT, flag_REDUCTION, "RTaut", flag_RTAUTOFF,
		  flag_RTAUTMIN, flag_RTAUTMAX);

  /* Activates the reduction rule Sort Simplification */
  flag_InitIntern(flag_RSSI, flag_REDUCTION, "RSSi", flag_RSSIOFF,
		  flag_RSSIMIN, flag_RSSIMAX);

  /* Activates static soft typing */
  flag_InitIntern(flag_RSST, flag_REDUCTION, "RSST", flag_RSSTOFF,
		  flag_RSSTMIN, flag_RSSTMAX);

  /* Activates Assignment Equation Deletion */
  /* If set to 2 it also eliminates equations */
  /* that are redundant only in non-trivial domains */
  flag_InitIntern(flag_RAED, flag_REDUCTION, "RAED", flag_RAEDOFF,
		  flag_RAEDMIN, flag_RAEDMAX);

  /* Activates Condensing */
  flag_InitIntern(flag_RCON, flag_REDUCTION, "RCon", flag_RCONOFF,
		  flag_RCONMIN, flag_RCONMAX);

  /* Activates reduction of input clauses */
  flag_InitIntern(flag_RINPUT, flag_UNIQUE, "RInput", flag_RINPUTON,
		  flag_RINPUTMIN, flag_RINPUTMAX);

  /* Activates application of definitions */
  flag_InitIntern(flag_APPLYDEFS, flag_UNIQUE, "ApplyDefs", flag_APPLYDEFSOFF,
		  flag_APPLYDEFSMIN, flag_APPLYDEFSMAX);

  /* If true usable and worked off are completely interreduced; otherwise only worked off */
  flag_InitIntern(flag_FULLRED, flag_UNIQUE, "FullRed", flag_FULLREDON,
		  flag_FULLREDMIN, flag_FULLREDMAX);

  /* Activates unit saturation of input clauses */
  flag_InitIntern(flag_SATINPUT, flag_UNIQUE, "SatInput", flag_SATINPUTOFF,
		  flag_SATINPUTMIN, flag_SATINPUTMAX);

  /* Ratio between weight and depth selection of clauses from usable */
  flag_InitIntern(flag_WDRATIO, flag_UNIQUE, "WDRatio", 5,
		  flag_WDRATIOMIN, flag_WDRATIOMAX);

  /* Factor to divide the weight of conjecture clauses to prefer them for selection */
  flag_InitIntern(flag_PREFCON, flag_UNIQUE, "PrefCon", flag_PREFCONUNCHANGED, 
		  flag_PREFCONMIN, flag_PREFCONMAX);

  /* Weight of a function symbol; weight of clause is used to select given */
  flag_InitIntern(flag_FUNCWEIGHT, flag_UNIQUE, "FuncWeight", 1,
		  flag_FUNCWEIGHTMIN, flag_FUNCWEIGHTMAX);

  /* Weight of a variable symbol; weight of clause is used to select given */
  flag_InitIntern(flag_VARWEIGHT, flag_UNIQUE, "VarWeight", 1,
		  flag_VARWEIGHTMIN, flag_VARWEIGHTMAX);

  /* Prefer the selection of clauses with many variable occurrences */
  flag_InitIntern(flag_PREFVAR, flag_UNIQUE, "PrefVar", flag_PREFVAROFF,
		  flag_PREFVARMIN, flag_PREFVARMAX);

  /* The type of bound: 0 (no bound) 1 (by clause weight) 2 (by clause term depth) */
  flag_InitIntern(flag_BOUNDMODE, flag_UNIQUE, "BoundMode", flag_BOUNDMODEUNLIMITED,
		  flag_BOUNDMODEMIN, flag_BOUNDMODEMAX);

  /* The initial bound value, where -1 means no restriction */
  flag_InitIntern(flag_BOUNDSTART, flag_UNIQUE, "BoundStart", flag_BOUNDSTARTUNLIMITED,
		  flag_BOUNDSTARTMIN, flag_BOUNDSTARTMAX);

  /* The number of bound saturation loops */
  flag_InitIntern(flag_BOUNDLOOPS, flag_UNIQUE, "BoundLoops", 1,
		  flag_BOUNDLOOPSMIN, flag_BOUNDLOOPSMAX);

  /* Flags for selecting the ordering to use */
  flag_InitIntern(flag_ORD, flag_UNIQUE, "Ordering", flag_ORDKBO,
		  flag_ORDMIN, flag_ORDMAX);

  /* CNF flag, if set optimized skolemization is performed */
  flag_InitIntern(flag_CNFOPTSKOLEM, flag_UNIQUE, "CNFOptSkolem", flag_CNFOPTSKOLEMON,
		  flag_CNFOPTSKOLEMMIN, flag_CNFOPTSKOLEMMAX);

  /* CNF flag, restricts the number of optimized skolemization proof steps */
  flag_InitIntern(flag_CNFPROOFSTEPS, flag_UNIQUE, "CNFProofSteps", 100,
		  flag_CNFPROOFSTEPSMIN, flag_CNFPROOFSTEPSMAX);

  /* CNF flag, if set renaming is performed */
  flag_InitIntern(flag_CNFRENAMING, flag_UNIQUE, "CNFRenaming", flag_CNFRENAMINGON,
		  flag_CNFRENAMINGMIN, flag_CNFRENAMINGMAX);

  /* CNF flag, if set renaming is printed */
  flag_InitIntern(flag_CNFPRENAMING, flag_UNIQUE, "CNFPRenaming", flag_CNFPRENAMINGOFF,
		  flag_CNFPRENAMINGMIN, flag_CNFPRENAMINGMAX);

  /* CNF flag, if set strong skolemization is performed */
  flag_InitIntern(flag_CNFSTRSKOLEM, flag_UNIQUE, "CNFStrSkolem", flag_CNFSTRSKOLEMON,
		  flag_CNFSTRSKOLEMMIN, flag_CNFSTRSKOLEMMAX);

  /* CNF flag, if set reductions on equality literals are performed */
  flag_InitIntern(flag_CNFFEQREDUCTIONS, flag_UNIQUE, "CNFFEqR", flag_CNFFEQREDUCTIONSON,
		  flag_CNFFEQREDUCTIONSMIN, flag_CNFFEQREDUCTIONSMAX);

  /* dfg2otter flag, if set input options for otter are generated */
  flag_InitIntern(flag_TDFG2OTTEROPTIONS, flag_UNIQUE, "TDfg2OtterOptions", flag_TDFG2OTTEROPTIONSOFF,
		  flag_TDFG2OTTEROPTIONSMIN, flag_TDFG2OTTEROPTIONSMAX);
}


FLAGSTORE flag_DefaultStore(void)
/**************************************************************
  INPUT:   None.
  RETURNS: Default flag store.
***************************************************************/
{
  return flag_DEFAULTSTORE;
}


void flag_Print(FLAGSTORE Store)
/**************************************************************
  INPUT:   A FlagStore.
  RETURNS: Nothing.
  EFFECT:  Prints the values of all flags to stdout.
***************************************************************/
{
  flag_FPrint(stdout, Store);
}


void flag_FPrint(FILE* File, FLAGSTORE Store)
/**************************************************************
  INPUT:   A File to print to, and a FlagStore.
  RETURNS: Nothing.
  EFFECT:  Prints the values of all flags to File.
***************************************************************/
{
  FLAG_ID  i;
  char name[30];
  
  fputs("list_of_settings(SPASS).{*", File);

  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i+= (FLAG_ID) 3) {
    sprintf(name,"set_flag(%s,%d).", flag_Name(i), flag_GetFlagValue(Store, i));
    fprintf(File,"\n %-30s",name);
    if (i+1 < flag_MAXFLAG) {
      sprintf(name,"set_flag(%s,%d).", flag_Name(i+ (FLAG_ID) 1), flag_GetFlagValue(Store, i+ (FLAG_ID) 1));
      fprintf(File," %-30s",name);
      if (i+2 < flag_MAXFLAG) {
	sprintf(name," set_flag(%s,%d).", flag_Name(i+ (FLAG_ID) 2), flag_GetFlagValue(Store, i+ (FLAG_ID) 2));
	fprintf(File," %-30s",name);
      }
    }
  }
  fputs("*}\nend_of_list.\n", File);
}


BOOL flag_Lookup(const char* String)
/**************************************************************
  INPUT:   A string <String>.
  RETURNS: TRUE iff <String> is the string of a known flag.
***************************************************************/
{
  return (flag_Id(String) != -1);
}


FLAG_ID flag_Id(const char* String)
/**************************************************************
  INPUT:   A string <String>.
  RETURNS: The identification of the flag <String> if it exists
           -1 otherwise.
***************************************************************/
{
  FLAG_ID i;

  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i++)
    if (string_Equal(flag_Name(i), String))
      return i;

  return (FLAG_ID) -1;
}


const char* flag_Name(FLAG_ID Flag)
/**************************************************************
  INPUT:   A FlagId.
  RETURNS: The name of the flag <Flag>.
  EFFECT:  Looks up the name of the flag <Flag> and returns it,
           if it exists.
***************************************************************/
{
  flag_CheckFlagIdInRange(Flag);
 
  return(flag_PROPERTIES[Flag].name);
}


int flag_Minimum(FLAG_ID Flag)
/**************************************************************
  INPUT:   A FlagId.
  RETURNS: The first integer below the minimal legal value 
           of the flag.
***************************************************************/
{
  flag_CheckFlagIdInRange(Flag);
 
  return flag_PROPERTIES[Flag].minimum;
}


int flag_Maximum(FLAG_ID Flag)
/**************************************************************
  INPUT:   A FlagId.
  RETURNS: The first integer above the maximal legal value 
           of the flag.
***************************************************************/
{
  flag_CheckFlagIdInRange(Flag);
 
  return flag_PROPERTIES[Flag].maximum;
}


FLAG_TYPE flag_Type(FLAG_ID Flag)
/**************************************************************
  INPUT:   A FlagId.
  RETURNS: The flag type.
***************************************************************/
{
  flag_CheckFlagIdInRange(Flag);

  return flag_PROPERTIES[Flag].type;  
}


void flag_ClearInferenceRules(FLAGSTORE Store)
/**************************************************************
  INPUT:   A FlagStore.
  RETURNS: Nothing.
  EFFECT:  Turns all inference rules off.
***************************************************************/
{
  FLAG_ID i;

  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i++) {
    if (flag_IsInference(i))
      flag_SetFlagValue(Store, i, flag_OFF);
  }
}


void flag_ClearReductionRules(FLAGSTORE Store)
/**************************************************************
  INPUT:   A FlagStore.
  RETURNS: Nothing.
  EFFECT:  Turns all reduction rules off.
***************************************************************/
{
  FLAG_ID i;

  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i++) {
    if (flag_IsReduction(i)) {
        flag_SetFlagValue(Store, i, flag_OFF);
    }
  }
}


void flag_ClearPrinting(FLAGSTORE Store)
/**************************************************************
  INPUT:   A FlagStore.
  RETURNS: Nothing.
  EFFECT:  Turns all printing off.
***************************************************************/
{

  FLAG_ID i;

  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i++) {
    if (flag_IsPrinting(i))
      flag_SetFlagValue(Store, i, flag_OFF);
  }
}


void flag_SetReductionsToDefaults(FLAGSTORE Store)
/**************************************************************
  INPUT:   A FlagStore.
  RETURNS: Nothing.
  EFFECT:  Sets all reduction rules to defaults.
***************************************************************/
{

  FLAG_ID i;

  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i++) {
    if (flag_IsReduction(i))
      flag_SetFlagToDefault(Store, i);
  }
}


void flag_InitFlotterSubproofFlags(FLAGSTORE Source, FLAGSTORE Target)
/**************************************************************
  INPUT:   Two flag stores.
  RETURNS: Nothing.
  EFFECT:  Initializes the flag store <Target> to the values required by a
           Flotter subproof. The other flag store is needed to take over
           some flags, e.g. DOCPROOF.
***************************************************************/
{
  /* Deactivate printing */
  flag_ClearPrinting(Target);

  /* Deactivate inference rules */
  flag_ClearInferenceRules(Target);

  /* Set reductions to default values */
  flag_SetReductionsToDefaults(Target);

  flag_SetFlagToDefault(Target, flag_CNFFEQREDUCTIONS);
  flag_SetFlagToDefault(Target, flag_RINPUT);
 
  /* Copy flag_DOCPROOF and flag_CNFPROOFSTEPS */
  flag_TransferFlag(Source, Target, flag_DOCPROOF);  
  flag_TransferFlag(Source, Target, flag_CNFPROOFSTEPS);

  /* Activate BoundedDepthUnitResolution */
  flag_SetFlagValue(Target, flag_IBUR, flag_BOUNDEDDEPTHUNITRESOLUTIONON);

  /* Activate KBO */
  flag_SetFlagValue(Target, flag_ORD, flag_ORDKBO);

  /* Transfer Weights for Terms */
  flag_TransferFlag(Source, Target, flag_FUNCWEIGHT);  
  flag_TransferFlag(Source, Target, flag_VARWEIGHT);

  /* Transfer Selection Strategy, not needed for depth bounded */
  /* unit resolution (see above) but for other potentially useful inference rules */
  flag_TransferFlag(Source, Target, flag_SELECT);  
}


void flag_InitFlotterFlags(FLAGSTORE Source, FLAGSTORE Target)
/**************************************************************
  INPUT:   Two flag stores.
  RETURNS: Nothing.
  EFFECT:  Initalizes the flag store <Target> to the values required by
           Flotter. The other flag store is needed to set
           some flags, e.g. DOCPROOF.
***************************************************************/
{
  flag_InitFlotterSubproofFlags(Source, Target);

  /* Set ordering to default value */
  flag_SetFlagToDefault(Target, flag_ORD);

  /* Set weighting flags to default values */
  flag_SetFlagToDefault(Target, flag_FUNCWEIGHT);
  flag_SetFlagToDefault(Target, flag_VARWEIGHT);

  /* Copy given values to diverse flags */
  flag_TransferFlag(Source, Target, flag_CNFRENAMING);
  flag_TransferFlag(Source, Target, flag_CNFOPTSKOLEM);
  flag_TransferFlag(Source, Target, flag_CNFSTRSKOLEM);
  flag_TransferFlag(Source, Target, flag_PAPPLYDEFS);
  flag_TransferFlag(Source, Target, flag_PBDC);
  flag_TransferFlag(Source, Target, flag_PBINC);
  flag_TransferFlag(Source, Target, flag_CNFPRENAMING);
  flag_TransferFlag(Source, Target, flag_POPTSKOLEM);
  flag_TransferFlag(Source, Target, flag_PSTRSKOLEM);
  flag_TransferFlag(Source, Target, flag_INTERACTIVE);
}


void flag_CheckStore(FLAGSTORE Store) 
/**************************************************************
  INPUT:   A flag store.
  RETURNS: TRUE is the flag store is in a valid state,
           FALSE otherwise.
***************************************************************/
{
  FLAG_ID i;
  FLAG value;

  /* check all flags */
  for (i = (FLAG_ID) 0; i < flag_MAXFLAG; i ++) {
    /* Get flag value first. We can't use flag_GetFlagValue() since it
       prints an error message and exits, if a flag is clean. A flag can
       be clean, only reading it is an error (for most functions).
    */

    value = Store[i];
    if (value != flag_CLEAN) {
      flag_CheckFlagValueInRange(i,value);
    }
  }
}
