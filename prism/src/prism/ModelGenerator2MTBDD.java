//==============================================================================
//	
//	Copyright (c) 2002-
//	Authors:
//	* Dave Parker <d.a.parker@cs.bham.ac.uk> (University of Birmingham)
//	
//------------------------------------------------------------------------------
//	
//	This file is part of PRISM.
//	
//	PRISM is free software; you can redistribute it and/or modify
//	it under the terms of the GNU General Public License as published by
//	the Free Software Foundation; either version 2 of the License, or
//	(at your option) any later version.
//	
//	PRISM is distributed in the hope that it will be useful,
//	but WITHOUT ANY WARRANTY; without even the implied warranty of
//	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//	GNU General Public License for more details.
//	
//	You should have received a copy of the GNU General Public License
//	along with PRISM; if not, write to the Free Software Foundation,
//	Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
//	
//==============================================================================

package prism;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.BitSet;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Vector;
import java.util.Map.Entry;

import common.IterableStateSet;
import explicit.Distribution;
import jdd.JDD;
import jdd.JDDNode;
import jdd.JDDVars;
import parser.State;
import parser.Values;
import parser.VarList;
import parser.ast.ModulesFile;

/**
 * Class to construct a symbolic representation from a ModelGenerator object.
 */
public class ModelGenerator2MTBDD
{
	// Prism stuff
	private Prism prism;
	private PrismLog mainLog;

	// Source model generator
	private ModelGenerator modelGen;

	// Model info
	private ModelType modelType;
	private VarList varList;
	private int numVars;

	// mtbdd stuff

	// dds/dd vars - whole system
	private JDDNode trans; // transition matrix dd
	private JDDNode range; // dd giving range for system
	private JDDNode start; // dd for start state
	private JDDNode reach; // dd for reachable states
	private JDDNode stateRewards; // dd of state rewards
	private JDDNode transRewards; // dd of transition rewards
	private JDDVars allDDRowVars; // all dd vars (rows)
	private JDDVars allDDColVars; // all dd vars (cols)
	private JDDVars allDDSynchVars; // all dd vars (synchronising actions)
	private JDDVars allDDSchedVars; // all dd vars (scheduling)
	private JDDVars allDDChoiceVars; // all dd vars (internal non-det.)
	private JDDVars allDDNondetVars; // all dd vars (all non-det.)
	// dds/dd vars - modules
	private JDDVars[] moduleDDRowVars; // dd vars for each module (rows)
	private JDDVars[] moduleDDColVars; // dd vars for each module (cols)
	private JDDNode[] moduleRangeDDs; // dd giving range for each module
	private JDDNode[] moduleIdentities; // identity matrix for each module
	// dds/dd vars - variables
	private JDDVars[] varDDRowVars; // dd vars (row/col) for each module variable
	private JDDVars[] varDDColVars;
	private JDDNode[] varRangeDDs; // dd giving range for each module variable
	private JDDNode[] varColRangeDDs; // dd giving range for each module variable (in col vars)
	private JDDNode[] varIdentities; // identity matrix for each module variable
	// dds/dd vars - nondeterminism
	private JDDNode[] ddSynchVars; // individual dd vars for synchronising actions
	private JDDNode[] ddSchedVars; // individual dd vars for scheduling non-det.
	private JDDNode[] ddChoiceVars; // individual dd vars for local non-det.
	// names for all dd vars used
	private Vector<String> ddVarNames;
	// action info
	private Vector<String> synchs; // list of action names
	private JDDNode transActions; // dd for transition action labels (MDPs)
	private Vector<JDDNode> transPerAction; // dds for transition action labels (D/CTMCs)

	private int maxNumChoices = 0;
	private LinkedHashMap<String, JDDNode> labelsDD;

	public ModelGenerator2MTBDD(Prism prism)
	{
		this.prism = prism;
		mainLog = prism.getMainLog();
	}

	/**
	 * Build a Model corresponding to the passed in model generator.
	 */
	public Model build(ModelGenerator modelGen) throws PrismException
	{
		this.modelGen = modelGen;
		modelType = modelGen.getModelType();
		varList = modelGen.createVarList();
		numVars = varList.getNumVars();
		return buildModel();
	}

	/** build model */
	private Model buildModel() throws PrismException
	{
		Model model = null;
		JDDNode tmp, tmp2;
		JDDVars ddv;
		int i;

		// for an mdp, compute the max number of choices in a state
		if (modelType == ModelType.MDP)
			maxNumChoices = 20; // TODO: fixme

		// allocate dd variables
		allocateDDVars();
		sortDDVars();
		sortIdentities();
		sortRanges();

		// construct transition matrix from file
		buildTrans();

		// get rid of any nondet dd variables not needed
		if (modelType == ModelType.MDP) {
			tmp = JDD.GetSupport(trans);
			tmp = JDD.ThereExists(tmp, allDDRowVars);
			tmp = JDD.ThereExists(tmp, allDDColVars);
			tmp2 = tmp;
			ddv = new JDDVars();
			while (!tmp2.equals(JDD.ONE)) {
				ddv.addVar(JDD.Var(tmp2.getIndex()));
				tmp2 = tmp2.getThen();
			}
			JDD.Deref(tmp);
			allDDNondetVars.derefAll();
			allDDNondetVars = ddv;
		}

		// 		// print dd variables actually used (support of trans)
		// 		mainLog.print("\nMTBDD variables used (" + allDDRowVars.n() + "r, " + allDDRowVars.n() + "c");
		// 		if (modelType == ModelType.MDP) mainLog.print(", " + allDDNondetVars.n() + "nd");
		// 		mainLog.print("):");
		// 		tmp = JDD.GetSupport(trans);
		// 		tmp2 = tmp;
		// 		while (!tmp2.isConstant()) {
		// 			//mainLog.print(" " + tmp2.getIndex() + ":" + ddVarNames.elementAt(tmp2.getIndex()));
		// 			mainLog.print(" " + ddVarNames.elementAt(tmp2.getIndex()));
		// 			tmp2 = tmp2.getThen();
		// 		}
		// 		mainLog.println();
		// 		JDD.Deref(tmp);

		// load labels
		//loadLabels();

		// compute state rewards
		//computeStateRewards();
		stateRewards = JDD.Constant(0);

		int numModules = 1; // just one module
		String moduleNames[] = new String[] { "M" };
		Values constantValues = new Values(); // no constants

		JDDNode stateRewardsArray[] = new JDDNode[1];
		stateRewardsArray[0] = stateRewards;
		JDDNode transRewardsArray[] = new JDDNode[1];
		transRewardsArray[0] = transRewards;
		String rewardStructNames[] = new String[1];
		rewardStructNames[0] = "";

		// create new Model object to be returned
		if (modelType == ModelType.DTMC) {
			model = new ProbModel(trans, start, stateRewardsArray, transRewardsArray, rewardStructNames, allDDRowVars, allDDColVars, ddVarNames, numModules,
					moduleNames, moduleDDRowVars, moduleDDColVars, numVars, varList, varDDRowVars, varDDColVars, constantValues);
		} else if (modelType == ModelType.MDP) {
			model = new NondetModel(trans, start, stateRewardsArray, transRewardsArray, rewardStructNames, allDDRowVars, allDDColVars, allDDSynchVars,
					allDDSchedVars, allDDChoiceVars, allDDNondetVars, ddVarNames, numModules, moduleNames, moduleDDRowVars, moduleDDColVars, numVars, varList,
					varDDRowVars, varDDColVars, constantValues);
		} else if (modelType == ModelType.CTMC) {
			model = new StochModel(trans, start, stateRewardsArray, transRewardsArray, rewardStructNames, allDDRowVars, allDDColVars, ddVarNames, numModules,
					moduleNames, moduleDDRowVars, moduleDDColVars, numVars, varList, varDDRowVars, varDDColVars, constantValues);
		}
		// set action info
		// TODO: disable if not required?
		model.setSynchs(synchs);
		if (modelType != ModelType.MDP) {
			model.setTransPerAction((JDDNode[]) transPerAction.toArray(new JDDNode[0]));
		} else {
			model.setTransActions(transActions);
		}

		// no need to do reachability
		model.setReach(reach);
		model.filterReachableStates();

		// Print some info (if extraddinfo flag on)
		if (prism.getExtraDDInfo()) {
			mainLog.print("Reach: " + JDD.GetNumNodes(model.getReach()) + " nodes\n");
		}

		// find any deadlocks
		model.findDeadlocks(prism.getFixDeadlocks());

		// attach labels (might overwrite deadlock state information)
		attachLabels(model);

		// deref spare dds
		JDD.Deref(moduleIdentities[0]);
		JDD.Deref(moduleRangeDDs[0]);
		for (i = 0; i < numVars; i++) {
			JDD.Deref(varIdentities[i]);
			JDD.Deref(varRangeDDs[i]);
			JDD.Deref(varColRangeDDs[i]);
		}
		JDD.Deref(range);
		if (modelType == ModelType.MDP) {
			for (i = 0; i < ddSynchVars.length; i++) {
				JDD.Deref(ddSynchVars[i]);
			}
			for (i = 0; i < ddSchedVars.length; i++) {
				JDD.Deref(ddSchedVars[i]);
			}
			for (i = 0; i < ddChoiceVars.length; i++) {
				JDD.Deref(ddChoiceVars[i]);
			}
		}
		if (labelsDD != null) {
			for (JDDNode d : labelsDD.values()) {
				JDD.Deref(d);
			}
		}

		return model;
	}

	/**
	 * allocate DD vars for system
	 * i.e. decide on variable ordering and request variables from CUDD
	 */
	private void allocateDDVars()
	{
		JDDNode v, vr, vc;
		int i, j, n;
		int ddVarsUsed = 0;
		ddVarNames = new Vector<String>();

		// create arrays/etc. first

		// nondeterministic variables
		if (modelType == ModelType.MDP) {
			ddSynchVars = new JDDNode[0];
			ddSchedVars = new JDDNode[0];
			ddChoiceVars = new JDDNode[maxNumChoices];
		}
		// module variable (row/col) vars
		varDDRowVars = new JDDVars[numVars];
		varDDColVars = new JDDVars[numVars];
		for (i = 0; i < numVars; i++) {
			varDDRowVars[i] = new JDDVars();
			varDDColVars[i] = new JDDVars();
		}

		// now allocate variables

		// allocate nondeterministic variables
		if (modelType == ModelType.MDP) {
			for (i = 0; i < maxNumChoices; i++) {
				v = JDD.Var(ddVarsUsed++);
				ddChoiceVars[i] = v;
				ddVarNames.add("l" + i);
			}
		}

		// allocate dd variables for module variables (i.e. rows/cols)
		// go through all vars in order (incl. global variables)
		// so overall ordering can be specified by ordering in the input file
		for (i = 0; i < numVars; i++) {
			// get number of dd variables needed
			// (ceiling of log2 of range of variable)
			n = varList.getRangeLogTwo(i);
			// add pairs of variables (row/col)
			for (j = 0; j < n; j++) {
				// new dd row variable
				vr = JDD.Var(ddVarsUsed++);
				// new dd col variable
				vc = JDD.Var(ddVarsUsed++);
				varDDRowVars[i].addVar(vr);
				varDDColVars[i].addVar(vc);
				// add names to list
				ddVarNames.add(varList.getName(i) + "." + j);
				ddVarNames.add(varList.getName(i) + "'." + j);
			}
		}
	}

	/**
	 * sort out DD variables and the arrays they are stored in
	 * (more than one copy of most variables is stored)
	 */
	private void sortDDVars()
	{
		int i;

		// put refs for all vars in each module together
		// create arrays
		moduleDDRowVars = new JDDVars[1];
		moduleDDColVars = new JDDVars[1];
		moduleDDRowVars[0] = new JDDVars();
		moduleDDColVars[0] = new JDDVars();
		// go thru all variables
		for (i = 0; i < numVars; i++) {
			moduleDDRowVars[0].copyVarsFrom(varDDRowVars[i]);
			moduleDDColVars[0].copyVarsFrom(varDDColVars[i]);
		}

		// put refs for all vars in whole system together
		// create arrays
		allDDRowVars = new JDDVars();
		allDDColVars = new JDDVars();
		if (modelType == ModelType.MDP) {
			allDDSynchVars = new JDDVars();
			allDDSchedVars = new JDDVars();
			allDDChoiceVars = new JDDVars();
			allDDNondetVars = new JDDVars();
		}
		// go thru all variables
		for (i = 0; i < numVars; i++) {
			// add to list
			allDDRowVars.copyVarsFrom(varDDRowVars[i]);
			allDDColVars.copyVarsFrom(varDDColVars[i]);
		}
		if (modelType == ModelType.MDP) {
			for (i = 0; i < ddChoiceVars.length; i++) {
				// add to list
				JDD.Ref(ddChoiceVars[i]);
				JDD.Ref(ddChoiceVars[i]);
				allDDChoiceVars.addVar(ddChoiceVars[i]);
				allDDNondetVars.addVar(ddChoiceVars[i]);
			}
		}
	}

	/** sort DDs for identities */
	private void sortIdentities()
	{
		int i, j;
		JDDNode id;

		// variable identities
		varIdentities = new JDDNode[numVars];
		for (i = 0; i < numVars; i++) {
			// set each element of the identity matrix
			id = JDD.Constant(0);
			for (j = 0; j < varList.getRange(i); j++) {
				id = JDD.SetMatrixElement(id, varDDRowVars[i], varDDColVars[i], j, j, 1);
			}
			varIdentities[i] = id;
		}
		// module identities
		moduleIdentities = new JDDNode[1];
		// product of identities for vars in module
		id = JDD.Constant(1);
		for (j = 0; j < numVars; j++) {
			if (varList.getModule(j) == 0) {
				JDD.Ref(varIdentities[j]);
				id = JDD.Apply(JDD.TIMES, id, varIdentities[j]);
			}
		}
		moduleIdentities[0] = id;
	}

	/** Sort DDs for ranges */
	private void sortRanges()
	{
		int i;

		// initialise range for whole system
		range = JDD.Constant(1);

		// variable ranges		
		varRangeDDs = new JDDNode[numVars];
		varColRangeDDs = new JDDNode[numVars];
		for (i = 0; i < numVars; i++) {
			// obtain range dd by abstracting from identity matrix
			JDD.Ref(varIdentities[i]);
			varRangeDDs[i] = JDD.SumAbstract(varIdentities[i], varDDColVars[i]);
			// obtain range dd by abstracting from identity matrix
			JDD.Ref(varIdentities[i]);
			varColRangeDDs[i] = JDD.SumAbstract(varIdentities[i], varDDRowVars[i]);
			// build up range for whole system as we go
			JDD.Ref(varRangeDDs[i]);
			range = JDD.Apply(JDD.TIMES, range, varRangeDDs[i]);
		}
		// module ranges
		moduleRangeDDs = new JDDNode[1];
		// obtain range dd by abstracting from identity matrix
		JDD.Ref(moduleIdentities[0]);
		moduleRangeDDs[0] = JDD.SumAbstract(moduleIdentities[0], moduleDDColVars[0]);
	}

	/** Construct transition matrix from file */
	private void buildTrans() throws PrismException
	{
		JDDNode elem, tmp;

		// initialise action list
		synchs = new Vector<String>();

		// initialise mtbdds
		trans = JDD.Constant(0);
		transRewards = JDD.Constant(0);
		if (modelType != ModelType.MDP) {
			transPerAction = new Vector<JDDNode>();
			transPerAction.add(JDD.Constant(0));
		} else {
			transActions = JDD.Constant(0);
		}
		start = JDD.Constant(0); 
		reach = JDD.Constant(0); 

		LinkedList<State> explore = new LinkedList<State>();
		// Add initial state(s) to 'explore', update start/reach
		for (State initState : modelGen.getInitialStates()) {
			explore.add(initState);
			JDDNode ddState = encodeState(initState, varDDRowVars);
			start = JDD.Or(start, ddState.copy());
			reach = JDD.Or(reach, ddState);
		}
		// Explore...
		while (!explore.isEmpty()) {
			// Pick next state to explore
			State state = explore.removeFirst();
			JDDNode ddState = encodeState(state, varDDRowVars);
			// Explore all choices/transitions from this state
			modelGen.exploreState(state);
			// Look at each outgoing choice in turn
			int nc = modelGen.getNumChoices();
			for (int i = 0; i < nc; i++) {
				Object o = modelGen.getChoiceAction(i);
				String a = o == null ? null : o.toString();
				// Look at each transition in the choice
				int nt = modelGen.getNumTransitions(i);
				for (int j = 0; j < nt; j++) {
					State stateNew = modelGen.computeTransitionTarget(i, j);
					double d = modelGen.getTransitionProbability(i, j);
					JDDNode ddStateNew = encodeState(stateNew, varDDRowVars);
					// Is this a new state?
					if (!JDD.AreIntersecting(reach, ddStateNew)) {
						// If so, add to the explore list
						explore.add(stateNew);
						// And to model
						reach = JDD.Or(reach, ddStateNew.copy());
					}
					// Build MTBDD for transition
					elem = JDD.Apply(JDD.TIMES, ddState.copy(), JDD.PermuteVariables(ddStateNew.copy(), allDDRowVars, allDDColVars));
					if (modelType == ModelType.MDP) {
						elem = JDD.Apply(JDD.TIMES, elem, JDD.SetVectorElement(JDD.Constant(0), allDDChoiceVars, i, 1));
					}
					// add it into mtbdds for transition matrix and transition rewards
					JDD.Ref(elem);
					trans = JDD.Apply(JDD.PLUS, trans, JDD.Apply(JDD.TIMES, JDD.Constant(d), elem));
					// look up action name
					int k;
					if (!("".equals(a))) {
						k = synchs.indexOf(a);
						// add to list if first time seen 
						if (k == -1) {
							synchs.add(a);
							k = synchs.size() - 1;
						}
						k++;
					} else {
						k = 0;
					}
					/// ...for dtmcs/ctmcs...
					if (modelType != ModelType.MDP) {
						// get (or create) dd for action k
						if (k < transPerAction.size()) {
							tmp = transPerAction.get(k);
						} else {
							tmp = JDD.Constant(0);
							transPerAction.add(tmp);
						}
						// add element to matrix
						JDD.Ref(elem);
						tmp = JDD.Apply(JDD.PLUS, tmp, JDD.Apply(JDD.TIMES, JDD.Constant(d), elem));
						transPerAction.set(j, tmp);
					}
					/// ...for mdps...
					else {
						JDD.Ref(elem);
						tmp = JDD.ThereExists(elem, allDDColVars);
						// use max here because we see multiple transitions for a sinlge choice
						transActions = JDD.Apply(JDD.MAX, transActions, JDD.Apply(JDD.TIMES, JDD.Constant(j), tmp));
					}
					// deref element dd
					JDD.Deref(elem);
					JDD.Deref(ddStateNew);
				}
				// Print some progress info occasionally
				// TODO progress.updateIfReady(src + 1);
			}
			JDD.Deref(ddState);
		}
		
		
		
		
	}

	/** Load label information form label file (if exists) */
	
	/*
	private void loadLabels() throws PrismException
	{
		if (labelsFile == null) {
			return;
		}

		// we construct BitSets for the labels
		Map<String, BitSet> labels = explicit.StateModelChecker.loadLabelsFile(labelsFile.getAbsolutePath());
		labelsDD = new LinkedHashMap<>();

		for (Entry<String, BitSet> e : labels.entrySet()) {
			// compute dd

			JDDNode labelStatesDD = JDD.Constant(0);

			for (int state : new IterableStateSet(e.getValue(), numStates)) {
				JDDNode tmp;
				// case where we don't have a state list...
				if (statesFile == null) {
					tmp = JDD.SetVectorElement(JDD.Constant(0), varDDRowVars[0], state, 1);
				}
				// case where we do have a state list...
				else {
					tmp = JDD.Constant(1);
					for (int i = 0; i < numVars; i++) {
						tmp = JDD.Apply(JDD.TIMES, tmp, JDD.SetVectorElement(JDD.Constant(0), varDDRowVars[i], statesArray[state][i], 1));
					}
				}

				// add it into bdd
				labelStatesDD = JDD.Or(labelStatesDD, tmp);
			}

			// store the dd
			labelsDD.put(e.getKey(), labelStatesDD);
		}
	}

*/

	/** Attach the computed label information to the model */
	private void attachLabels(Model model) throws PrismNotSupportedException
	{
		if (labelsDD == null)
			return;

		for (Entry<String, JDDNode> e : labelsDD.entrySet()) {
			if (e.equals("init")) {
				// handled in model construction
				continue;
			}
			model.addLabelDD(e.getKey(), e.getValue().copy());
		}
	}

	/** Read info about state rewards from a .srew file */
	
	/*
	private void computeStateRewards() throws PrismException
	{
		String s, ss[];
		int i, j, lineNum = 0;
		double d;
		JDDNode tmp;

		// initialise mtbdd
		stateRewards = JDD.Constant(0);

		if (stateRewardsFile == null)
			return;

		// open file for reading, automatic close when done
		try (BufferedReader in = new BufferedReader(new FileReader(stateRewardsFile))) {
			// skip first line
			in.readLine();
			lineNum = 1;
			// read remaining lines
			s = in.readLine();
			lineNum++;
			while (s != null) {
				// skip blank lines
				s = s.trim();
				if (s.length() > 0) {
					// split into two parts
					ss = s.split(" ");
					if (ss.length != 2)
						throw new PrismException("");
					// determine which state this line refers to
					i = Integer.parseInt(ss[0]);
					// determine reward value
					d = Double.parseDouble(ss[1]);
					// construct element of vector mtbdd
					// case where we don't have a state list...
					if (statesFile == null) {
						tmp = JDD.SetVectorElement(JDD.Constant(0), varDDRowVars[0], i, 1.0);
					}
					// case where we do have a state list...
					else {
						tmp = JDD.Constant(1);
						for (j = 0; j < numVars; j++) {
							tmp = JDD.Apply(JDD.TIMES, tmp, JDD.SetVectorElement(JDD.Constant(0), varDDRowVars[j], statesArray[i][j], 1));
						}
					}
					// add it into mtbdd for state rewards
					stateRewards = JDD.Apply(JDD.PLUS, stateRewards, JDD.Apply(JDD.TIMES, JDD.Constant(d), tmp));
				}
				// read next line
				s = in.readLine();
				lineNum++;
			}
		} catch (IOException e) {
			throw new PrismException("File I/O error reading from \"" + stateRewardsFile + "\": " + e.getMessage());
		} catch (NumberFormatException e) {
			throw new PrismException("Error detected at line " + lineNum + " of state rewards file \"" + stateRewardsFile + "\"");
		} catch (PrismException e) {
			throw new PrismException("Error detected " + e.getMessage() + "at line " + lineNum + " of state rewards file \"" + stateRewardsFile + "\"");
		}
	}

	*/
	
	/**
	 * Encode a state into a BDD (referencing the result).
	 */
	private JDDNode encodeState(State state, JDDVars[] varDDVars)
	{
		JDDNode res;
		int i, j = 0;
		res = JDD.Constant(1);
		for (i = 0; i < numVars; i++) {
			try {
				j = varList.encodeToInt(i, state.varValues[i]);
			} catch (PrismLangException e) {
				// Won't happen
			}
			res = JDD.Apply(JDD.TIMES, res, JDD.SetVectorElement(JDD.Constant(0), varDDVars[i], j, 1.0));
		}
		return res;
	}
}

//------------------------------------------------------------------------------