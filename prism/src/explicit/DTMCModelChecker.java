//==============================================================================
//	
//	Copyright (c) 2002-
//	Authors:
//	* Dave Parker <david.parker@comlab.ox.ac.uk> (University of Oxford)
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

package explicit;

import java.io.File;
import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import org.gnu.glpk.GLPK;
import org.gnu.glpk.GLPKConstants;
import org.gnu.glpk.SWIGTYPE_p_double;
import org.gnu.glpk.SWIGTYPE_p_int;
import org.gnu.glpk.glp_prob;
import org.gnu.glpk.glp_smcp;

import parser.VarList;
import parser.ast.Declaration;
import parser.ast.DeclarationIntUnbounded;
import parser.ast.Expression;
import prism.Prism;
import prism.PrismComponent;
import prism.PrismException;
import prism.PrismFileLog;
import prism.PrismUtils;
import acceptance.AcceptanceReach;
import acceptance.AcceptanceType;
import common.IterableBitSet;
import explicit.rewards.MCRewards;
import explicit.rewards.Rewards;

/**
 * Explicit-state model checker for discrete-time Markov chains (DTMCs).
 */
public class DTMCModelChecker extends ProbModelChecker
{
	/**
	 * Create a new DTMCModelChecker, inherit basic state from parent (unless null).
	 */
	public DTMCModelChecker(PrismComponent parent) throws PrismException
	{
		super(parent);
	}

	// Model checking functions

	@Override
	protected StateValues checkProbPathFormulaLTL(Model model, Expression expr, boolean qual, MinMax minMax, BitSet statesOfInterest) throws PrismException
	{
		LTLModelChecker mcLtl;
		StateValues probsProduct, probs;
		LTLModelChecker.LTLProduct<DTMC> product;
		DTMCModelChecker mcProduct;

		// For LTL model checking routines
		mcLtl = new LTLModelChecker(this);

		// Build product of Markov chain and automaton
		AcceptanceType[] allowedAcceptance = {
				AcceptanceType.RABIN,
				AcceptanceType.REACH,
				AcceptanceType.GENERIC
		};
		product = mcLtl.constructProductMC(this, (DTMC)model, expr, statesOfInterest, allowedAcceptance);

		// Output product, if required
		if (getExportProductTrans()) {
				mainLog.println("\nExporting product transition matrix to file \"" + getExportProductTransFilename() + "\"...");
				product.getProductModel().exportToPrismExplicitTra(getExportProductTransFilename());
		}
		if (getExportProductStates()) {
			mainLog.println("\nExporting product state space to file \"" + getExportProductStatesFilename() + "\"...");
			PrismFileLog out = new PrismFileLog(getExportProductStatesFilename());
			VarList newVarList = (VarList) modulesFile.createVarList().clone();
			String daVar = "_da";
			while (newVarList.getIndex(daVar) != -1) {
				daVar = "_" + daVar;
			}
			newVarList.addVar(0, new Declaration(daVar, new DeclarationIntUnbounded()), 1, null);
			product.getProductModel().exportStates(Prism.EXPORT_PLAIN, newVarList, out);
			out.close();
		}
		
		// Find accepting states + compute reachability probabilities
		BitSet acc;
		if (product.getAcceptance() instanceof AcceptanceReach) {
			mainLog.println("\nSkipping BSCC computation since acceptance is defined via goal states...");
			acc = ((AcceptanceReach)product.getAcceptance()).getGoalStates();
		} else {
			mainLog.println("\nFinding accepting BSCCs...");
			acc = mcLtl.findAcceptingBSCCs(product.getProductModel(), product.getAcceptance());
		}
		mainLog.println("\nComputing reachability probabilities...");
		mcProduct = new DTMCModelChecker(this);
		mcProduct.inheritSettings(this);
		ModelCheckerResult res = mcProduct.computeReachProbs(product.getProductModel(), acc); 
		probsProduct = StateValues.createFromDoubleArray(res.soln, product.getProductModel());

		// Output vector over product, if required
		if (getExportProductVector()) {
				mainLog.println("\nExporting product solution vector matrix to file \"" + getExportProductVectorFilename() + "\"...");
				PrismFileLog out = new PrismFileLog(getExportProductVectorFilename());
				probsProduct.print(out, false, false, false, false);
				out.close();
		}
		
		// Mapping probabilities in the original model
		probs = product.projectToOriginalModel(probsProduct);
		probsProduct.clear();

		return probs;
	}

	/**
	 * Compute rewards for a co-safe LTL reward operator.
	 */
	protected StateValues checkRewardCoSafeLTL(Model model, Rewards modelRewards, Expression expr, MinMax minMax, BitSet statesOfInterest) throws PrismException
	{
		LTLModelChecker mcLtl;
		MCRewards productRewards;
		StateValues rewardsProduct, rewards;
		DTMCModelChecker mcProduct;
		LTLModelChecker.LTLProduct<DTMC> product;

		// For LTL model checking routines
		mcLtl = new LTLModelChecker(this);

		// Build product of Markov chain and automaton
		AcceptanceType[] allowedAcceptance = {
				AcceptanceType.RABIN,
				AcceptanceType.REACH
		};
		product = mcLtl.constructProductMC(this, (DTMC)model, expr, statesOfInterest, allowedAcceptance);
		
		// Adapt reward info to product model
		productRewards = ((MCRewards) modelRewards).liftFromModel(product);
		
		// Output product, if required
		if (getExportProductTrans()) {
				mainLog.println("\nExporting product transition matrix to file \"" + getExportProductTransFilename() + "\"...");
				product.getProductModel().exportToPrismExplicitTra(getExportProductTransFilename());
		}
		if (getExportProductStates()) {
			mainLog.println("\nExporting product state space to file \"" + getExportProductStatesFilename() + "\"...");
			PrismFileLog out = new PrismFileLog(getExportProductStatesFilename());
			VarList newVarList = (VarList) modulesFile.createVarList().clone();
			String daVar = "_da";
			while (newVarList.getIndex(daVar) != -1) {
				daVar = "_" + daVar;
			}
			newVarList.addVar(0, new Declaration(daVar, new DeclarationIntUnbounded()), 1, null);
			product.getProductModel().exportStates(Prism.EXPORT_PLAIN, newVarList, out);
			out.close();
		}
		
		// Find accepting states + compute reachability rewards
		BitSet acc;
		if (product.getAcceptance() instanceof AcceptanceReach) {
			mainLog.println("\nSkipping BSCC computation since acceptance is defined via goal states...");
			acc = ((AcceptanceReach)product.getAcceptance()).getGoalStates();
		} else {
			mainLog.println("\nFinding accepting BSCCs...");
			acc = mcLtl.findAcceptingBSCCs(product.getProductModel(), product.getAcceptance());
		}
		mainLog.println("\nComputing reachability probabilities...");
		mcProduct = new DTMCModelChecker(this);
		mcProduct.inheritSettings(this);
		ModelCheckerResult res = mcProduct.computeReachRewards(product.getProductModel(), productRewards, acc);
		rewardsProduct = StateValues.createFromDoubleArray(res.soln, product.getProductModel());
		
		// Output vector over product, if required
		if (getExportProductVector()) {
				mainLog.println("\nExporting product solution vector matrix to file \"" + getExportProductVectorFilename() + "\"...");
				PrismFileLog out = new PrismFileLog(getExportProductVectorFilename());
				rewardsProduct.print(out, false, false, false, false);
				out.close();
		}
		
		// Mapping rewards in the original model
		rewards = product.projectToOriginalModel(rewardsProduct);
		rewardsProduct.clear();
		
		return rewards;
	}
	
	public ModelCheckerResult computeInstantaneousRewards(DTMC dtmc, MCRewards mcRewards, int k, BitSet statesOfInterest) throws PrismException
	{
		if (statesOfInterest.cardinality() == 1) {
			return computeInstantaneousRewardsForwards(dtmc, mcRewards, k, statesOfInterest.nextSetBit(0));
		} else {
			return computeInstantaneousRewardsBackwards(dtmc, mcRewards, k);
		}
	}
	
	public ModelCheckerResult computeInstantaneousRewardsBackwards(DTMC dtmc, MCRewards mcRewards, int k) throws PrismException
	{
		ModelCheckerResult res = null;
		int i, n, iters;
		double soln[], soln2[], tmpsoln[];
		long timer;

		// Store num states
		n = dtmc.getNumStates();

		// Start backwards transient computation
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting backwards instantaneous rewards computation...");

		// Create solution vector(s)
		soln = new double[n];
		soln2 = new double[n];

		// Initialise solution vectors.
		for (i = 0; i < n; i++)
			soln[i] = mcRewards.getStateReward(i);

		// Start iterations
		for (iters = 0; iters < k; iters++) {
			// Matrix-vector multiply
			dtmc.mvMult(soln, soln2, null, false);
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished backwards transient computation
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Backwards transient instantaneous rewards computation");
		mainLog.println(" took " + iters + " iters and " + timer / 1000.0 + " seconds.");

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.lastSoln = soln2;
		res.numIters = iters;
		res.timeTaken = timer / 1000.0;
		res.timePre = 0.0;
		return res;
	}

	public ModelCheckerResult computeInstantaneousRewardsForwards(DTMC dtmc, MCRewards mcRewards, int k, int stateOfInterest) throws PrismException
	{
		// Build a point probability distribution for the required state  
		double[] initDist = new double[dtmc.getNumStates()];
		initDist[stateOfInterest] = 1.0;
		
		// Compute (forward) transient probabilities
		ModelCheckerResult res = computeTransientProbs(dtmc, k, initDist);
		
		// Compute expected value (from initial state)
		int n = dtmc.getNumStates();
		double avg = 0.0;
		for (int i = 0; i < n; i++) {
			avg += res.soln[i] *= mcRewards.getStateReward(i);
		}

		// Reuse vector/result storage
		for (int i = 0; i < n; i++) {
			res.soln[i] = 0.0;
		}
		res.soln[stateOfInterest] = avg;
		
		return res;
	}
	
	public ModelCheckerResult computeCumulativeRewards(DTMC dtmc, MCRewards mcRewards, double t) throws PrismException
	{
		ModelCheckerResult res = null;
		int i, n, iters;
		double soln[], soln2[], tmpsoln[];
		long timer;
		int right = (int) t;

		// Store num states
		n = dtmc.getNumStates();

		// Start backwards transient computation
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting backwards cumulative rewards computation...");

		// Create solution vector(s)
		soln = new double[n];
		soln2 = new double[n];

		// Start iterations
		for (iters = 0; iters < right; iters++) {
			// Matrix-vector multiply plus adding rewards
			dtmc.mvMult(soln, soln2, null, false);
			for (i = 0; i < n; i++) {
				soln2[i] += mcRewards.getStateReward(i);
			}
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished backwards transient computation
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Backwards cumulative rewards computation");
		mainLog.println(" took " + iters + " iters and " + timer / 1000.0 + " seconds.");

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.lastSoln = soln2;
		res.numIters = iters;
		res.timeTaken = timer / 1000.0;
		res.timePre = 0.0;
		return res;
	}

	public ModelCheckerResult computeTotalRewards(DTMC dtmc, MCRewards mcRewards) throws PrismException
	{
		ModelCheckerResult res = null;
		int n, numBSCCs = 0;
		long timer;

		// Switch to a supported method, if necessary
		if (!(linEqMethod == LinEqMethod.POWER)) {
			linEqMethod = LinEqMethod.POWER;
			mainLog.printWarning("Switching to linear equation solution method \"" + linEqMethod.fullName() + "\"");
		}

		// Store num states
		n = dtmc.getNumStates();

		// Start total rewards computation
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting total reward computation...");

		// Compute bottom strongly connected components (BSCCs)
		SCCComputer sccComputer = SCCComputer.createSCCComputer(this, dtmc);
		sccComputer.computeBSCCs();
		List<BitSet> bsccs = sccComputer.getBSCCs();
		numBSCCs = bsccs.size();

		// Find BSCCs with non-zero reward
		BitSet bsccsNonZero = new BitSet();
		for (int b = 0; b < numBSCCs; b++) {
			BitSet bscc = bsccs.get(b);
			for (int i = bscc.nextSetBit(0); i >= 0; i = bscc.nextSetBit(i + 1)) {
				if (mcRewards.getStateReward(i) > 0) {
					bsccsNonZero.or(bscc);
					break;
				}
			}
		}
		mainLog.print("States in non-zero reward BSCCs: " + bsccsNonZero.cardinality());
		
		// Find states with infinite reward (those reach a non-zero reward BSCC with prob > 0)
		BitSet inf;
		if (preRel) {
			// prob0 using predecessor relation
			PredecessorRelation pre = dtmc.getPredecessorRelation(this, true);
			inf = prob0(dtmc, null, bsccsNonZero, pre);
		} else {
			// prob0 using fixed point algorithm
			inf = prob0(dtmc, null, bsccsNonZero);
		}
		inf.flip(0, n);
		int numInf = inf.cardinality();
		mainLog.println(", inf=" + numInf + ", maybe=" + (n - numInf));
		
		// Compute rewards
		// (do this using the functions for "reward reachability" properties but with no targets)
		switch (linEqMethod) {
		case POWER:
			res = computeReachRewardsValIter(dtmc, mcRewards, new BitSet(), inf, null, null);
			break;
		default:
			throw new PrismException("Unknown linear equation solution method " + linEqMethod.fullName());
		}

		// Finished total reward computation
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Total reward computation");
		mainLog.println(" took " + timer / 1000.0 + " seconds.");

		// Return results
		return res;
	}

	// Steady-state/transient probability computation

	/**
	 * Compute steady-state probability distribution (forwards).
	 * Start from initial state (or uniform distribution over multiple initial states).
	 */
	public StateValues doSteadyState(DTMC dtmc) throws PrismException
	{
		return doSteadyState(dtmc, (StateValues) null);
	}

	/**
	 * Compute steady-state probability distribution (forwards).
	 * Optionally, use the passed in file initDistFile to give the initial probability distribution (time 0).
	 * If null, start from initial state (or uniform distribution over multiple initial states).
	 */
	public StateValues doSteadyState(DTMC dtmc, File initDistFile) throws PrismException
	{
		StateValues initDist = readDistributionFromFile(initDistFile, dtmc);
		return doSteadyState(dtmc, initDist);
	}

	/**
	 * Compute steady-state probability distribution (forwards).
	 * Optionally, use the passed in vector initDist as the initial probability distribution (time 0).
	 * If null, start from initial state (or uniform distribution over multiple initial states).
	 * For reasons of efficiency, when a vector is passed in, it will be trampled over,
	 * so if you wanted it, take a copy. 
	 * @param dtmc The DTMC
	 * @param initDist Initial distribution (will be overwritten)
	 */
	public StateValues doSteadyState(DTMC dtmc, StateValues initDist) throws PrismException
	{
		StateValues initDistNew = (initDist == null) ? buildInitialDistribution(dtmc) : initDist;
		ModelCheckerResult res = computeSteadyStateProbs(dtmc, initDistNew.getDoubleArray());
		return StateValues.createFromDoubleArray(res.soln, dtmc);
	}

	/**
	 * Compute transient probability distribution (forwards).
	 * Start from initial state (or uniform distribution over multiple initial states).
	 */
	public StateValues doTransient(DTMC dtmc, int k) throws PrismException
	{
		return doTransient(dtmc, k, (StateValues) null);
	}

	/**
	 * Compute transient probability distribution (forwards).
	 * Optionally, use the passed in file initDistFile to give the initial probability distribution (time 0).
	 * If null, start from initial state (or uniform distribution over multiple initial states).
	 * @param dtmc The DTMC
	 * @param k Time step
	 * @param initDistFile File containing initial distribution
	 */
	public StateValues doTransient(DTMC dtmc, int k, File initDistFile) throws PrismException
	{
		StateValues initDist = readDistributionFromFile(initDistFile, dtmc);
		return doTransient(dtmc, k, initDist);
	}

	/**
	 * Compute transient probability distribution (forwards).
	 * Optionally, use the passed in vector initDist as the initial probability distribution (time step 0).
	 * If null, start from initial state (or uniform distribution over multiple initial states).
	 * For reasons of efficiency, when a vector is passed in, it will be trampled over,
	 * so if you wanted it, take a copy. 
	 * @param dtmc The DTMC
	 * @param k Time step
	 * @param initDist Initial distribution (will be overwritten)
	 */
	public StateValues doTransient(DTMC dtmc, int k, StateValues initDist) throws PrismException
	{
		StateValues initDistNew = (initDist == null) ? buildInitialDistribution(dtmc) : initDist;
		ModelCheckerResult res = computeTransientProbs(dtmc, k, initDistNew.getDoubleArray());
		return StateValues.createFromDoubleArray(res.soln, dtmc);
	}

	// Numerical computation functions

	/**
	 * Compute next=state probabilities.
	 * i.e. compute the probability of being in a state in {@code target} in the next step.
	 * @param dtmc The DTMC
	 * @param target Target states
	 */
	public ModelCheckerResult computeNextProbs(DTMC dtmc, BitSet target) throws PrismException
	{
		ModelCheckerResult res = null;
		int n;
		double soln[], soln2[];
		long timer;

		timer = System.currentTimeMillis();

		// Store num states
		n = dtmc.getNumStates();

		// Create/initialise solution vector(s)
		soln = Utils.bitsetToDoubleArray(target, n);
		soln2 = new double[n];

		// Next-step probabilities 
		dtmc.mvMult(soln, soln2, null, false);

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln2;
		res.numIters = 1;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Given a value vector x, compute the probability:
	 *   v(s) = Sum_s' P(s,s')*x(s')   for s labeled with a,
	 *   v(s) = 0                      for s not labeled with a.
	 *
	 * @param dtmc the DTMC model
	 * @param a the set of states labeled with a
	 * @param x the value vector
	 */
	protected double[] computeRestrictedNext(DTMC dtmc, BitSet a, double[] x)
	{
		double[] soln;
		int n;

		// Store num states
		n = dtmc.getNumStates();

		// initialized to 0.0
		soln = new double[n];

		// Next-step probabilities multiplication
		// restricted to a states
		dtmc.mvMult(x, soln, a, false);

		return soln;
	}

	/**
	 * Compute reachability probabilities.
	 * i.e. compute the probability of reaching a state in {@code target}.
	 * @param dtmc The DTMC
	 * @param target Target states
	 */
	public ModelCheckerResult computeReachProbs(DTMC dtmc, BitSet target) throws PrismException
	{
		return computeReachProbs(dtmc, null, target, null, null);
	}

	/**
	 * Compute until probabilities.
	 * i.e. compute the probability of reaching a state in {@code target},
	 * while remaining in those in {@code remain}.
	 * @param dtmc The DTMC
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 */
	public ModelCheckerResult computeUntilProbs(DTMC dtmc, BitSet remain, BitSet target) throws PrismException
	{
		return computeReachProbs(dtmc, remain, target, null, null);
	}

	/**
	 * Compute reachability/until probabilities.
	 * i.e. compute the min/max probability of reaching a state in {@code target},
	 * while remaining in those in {@code remain}.
	 * @param dtmc The DTMC
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param init Optionally, an initial solution vector (may be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values.  
	 */
	public ModelCheckerResult computeReachProbs(DTMC dtmc, BitSet remain, BitSet target, double init[], BitSet known) throws PrismException
	{
		ModelCheckerResult res = null;
		BitSet no, yes;
		int n, numYes, numNo;
		long timer, timerProb0, timerProb1;
		PredecessorRelation pre = null;
		// Local copy of setting
		LinEqMethod linEqMethod = this.linEqMethod;

		// Switch to a supported method, if necessary
		if (!(linEqMethod == LinEqMethod.POWER || linEqMethod == LinEqMethod.GAUSS_SEIDEL
				|| linEqMethod == LinEqMethod.EXACT_LINEAR_PROGRAMMING || GLPK.EXACTLP_REQUIREMENTS == 0)) {
			linEqMethod = LinEqMethod.GAUSS_SEIDEL;
			mainLog.printWarning("Switching to linear equation solution method \"" + linEqMethod.fullName() + "\"");
		}

		// Start probabilistic reachability
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting probabilistic reachability...");

		// Check for deadlocks in non-target state (because breaks e.g. prob1)
		dtmc.checkForDeadlocks(target);

		// Store num states
		n = dtmc.getNumStates();

		// Optimise by enlarging target set (if more info is available)
		if (init != null && known != null && !known.isEmpty()) {
			BitSet targetNew = (BitSet) target.clone();
			for (int i : new IterableBitSet(known)) {
				if (init[i] == 1.0) {
					targetNew.set(i);
				}
			}
			target = targetNew;
		}

		// If required, export info about target states
		if (getExportTarget()) {
			BitSet bsInit = new BitSet(n);
			for (int i = 0; i < n; i++) {
				bsInit.set(i, dtmc.isInitialState(i));
			}
			List<BitSet> labels = Arrays.asList(bsInit, target);
			List<String> labelNames = Arrays.asList("init", "target");
			mainLog.println("\nExporting target states info to file \"" + getExportTargetFilename() + "\"...");
			exportLabels(dtmc, labels, labelNames, Prism.EXPORT_PLAIN, new PrismFileLog(getExportTargetFilename()));
		}

		if (precomp && (prob0 || prob1) && preRel) {
			pre = dtmc.getPredecessorRelation(this, true);
		}

		// Precomputation
		timerProb0 = System.currentTimeMillis();
		if (precomp && prob0) {
			if (preRel) {
				no = prob0(dtmc, remain, target, pre);
			} else {
				no = prob0(dtmc, remain, target);
			}
		} else {
			no = new BitSet();
		}
		timerProb0 = System.currentTimeMillis() - timerProb0;
		timerProb1 = System.currentTimeMillis();
		if (precomp && prob1) {
			if (preRel) {
				yes = prob1(dtmc, remain, target, pre);
			} else {
				yes = prob1(dtmc, remain, target);
			}
		} else {
			yes = (BitSet) target.clone();
		}
		timerProb1 = System.currentTimeMillis() - timerProb1;

		// Print results of precomputation
		numYes = yes.cardinality();
		numNo = no.cardinality();
		mainLog.println("target=" + target.cardinality() + ", yes=" + numYes + ", no=" + numNo + ", maybe=" + (n - (numYes + numNo)));

		// Compute probabilities
		switch (linEqMethod) {
		case POWER:
			res = computeReachProbsValIter(dtmc, no, yes, init, known);
			break;
		case GAUSS_SEIDEL:
			res = computeReachProbsGaussSeidel(dtmc, no, yes, init, known);
			break;
		case EXACT_LINEAR_PROGRAMMING:
			res = computeReachProbsExactLinearProg(dtmc, no, yes, init, known);
			break;
		default:
			throw new PrismException("Unknown linear equation solution method " + linEqMethod.fullName());
		}

		// Finished probabilistic reachability
		timer = System.currentTimeMillis() - timer;
		mainLog.println("Probabilistic reachability took " + timer / 1000.0 + " seconds.");

		// Update time taken
		res.timeTaken = timer / 1000.0;
		res.timeProb0 = timerProb0 / 1000.0;
		res.timePre = (timerProb0 + timerProb1) / 1000.0;

		return res;
	}


	/**
	 * Prob0 precomputation algorithm (using predecessor relation),
	 * i.e. determine the states of a DTMC which, with probability 0,
	 * reach a state in {@code target}, while remaining in those in {@code remain}.
	 * @param dtmc The DTMC
	 * @param remain Remain in these states (optional: {@code null} means "all states")
	 * @param target Target states
	 * @param pre The predecessor relation
	 */
	public BitSet prob0(DTMC dtmc, BitSet remain, BitSet target, PredecessorRelation pre)
	{
		BitSet canReachTarget, result;
		long timer;

		// Start precomputation
		timer = System.currentTimeMillis();
		mainLog.println("Starting Prob0...");

		// Special case: no target states
		if (target.isEmpty()) {
			BitSet soln = new BitSet(dtmc.getNumStates());
			soln.set(0, dtmc.getNumStates());
			return soln;
		}

		// calculate all states that can reach 'target'
		// while remaining in 'remain' in the underlying graph,
		// where all the 'target' states are made absorbing
		canReachTarget = pre.calculatePreStar(remain, target, target);

		// prob0 = complement of 'canReachTarget'
		result = new BitSet();
		result.set(0, dtmc.getNumStates(), true);
		result.andNot(canReachTarget);

		// Finished precomputation
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Prob0");
		mainLog.println(" took " + timer / 1000.0 + " seconds.");

		return result;
	}

	/**
	 * Prob0 precomputation algorithm (using a fixed-point computation),
	 * i.e. determine the states of a DTMC which, with probability 0,
	 * reach a state in {@code target}, while remaining in those in {@code remain}.
	 * @param dtmc The DTMC
	 * @param remain Remain in these states (optional: {@code null} means "all")
	 * @param target Target states
	 */
	public BitSet prob0(DTMC dtmc, BitSet remain, BitSet target)
	{
		int n, iters;
		BitSet u, soln, unknown;
		boolean u_done;
		long timer;

		// Start precomputation
		timer = System.currentTimeMillis();
		mainLog.println("Starting Prob0...");

		// Special case: no target states
		if (target.cardinality() == 0) {
			soln = new BitSet(dtmc.getNumStates());
			soln.set(0, dtmc.getNumStates());
			return soln;
		}

		// Initialise vectors
		n = dtmc.getNumStates();
		u = new BitSet(n);
		soln = new BitSet(n);

		// Determine set of states actually need to perform computation for
		unknown = new BitSet();
		unknown.set(0, n);
		unknown.andNot(target);
		if (remain != null)
			unknown.and(remain);

		// Fixed point loop
		iters = 0;
		u_done = false;
		// Least fixed point - should start from 0 but we optimise by
		// starting from 'target', thus bypassing first iteration
		u.or(target);
		soln.or(target);
		while (!u_done) {
			iters++;
			// Single step of Prob0
			dtmc.prob0step(unknown, u, soln);
			// Check termination
			u_done = soln.equals(u);
			// u = soln
			u.clear();
			u.or(soln);
		}

		// Negate
		u.flip(0, n);

		// Finished precomputation
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Prob0");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		return u;
	}

	/**
	 * Prob1 precomputation algorithm (using predecessor relation),
	 * i.e. determine the states of a DTMC which, with probability 1,
	 * reach a state in {@code target}, while remaining in those in {@code remain}.
	 * @param dtmc The DTMC
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param pre The predecessor relation of the DTMC
	 */
	public BitSet prob1(DTMC dtmc, BitSet remain, BitSet target, PredecessorRelation pre) {
		// Implements the constrained reachability algorithm from
		// Baier, Katoen: Principles of Model Checking (Corollary 10.31 Qualitative Constrained Reachability)
		long timer;

		// Start precomputation
		timer = System.currentTimeMillis();
		mainLog.println("Starting Prob1...");

		// Special case: no 'target' states
		if (target.isEmpty()) {
			// empty set
			return new BitSet();
		}

		// mark all states in 'target' and all states not in 'remain' as absorbing
		BitSet absorbing = new BitSet();
		if (remain != null) {
			// complement remain
			absorbing.set(0, dtmc.getNumStates(), true);
			absorbing.andNot(remain);
		} else {
			// for remain == null, remain consists of all states
			// thus, absorbing = the empty set is already the complementation of remain
		}
		// union with 'target'
		absorbing.or(target);

		// M' = DTMC where all 'absorbing' states are considered to be absorbing

		// the set of states that satisfy E [ F target ] in M'
		// Pre*(target)
		BitSet canReachTarget = pre.calculatePreStar(null, target, absorbing);

		// complement canReachTarget
		// S\Pre*(target)
		BitSet canNotReachTarget = new BitSet();
		canNotReachTarget.set(0, dtmc.getNumStates(), true);
		canNotReachTarget.andNot(canReachTarget);

		// the set of states that can reach a canNotReachTarget state in M'
		// Pre*(S\Pre*(target))
		BitSet probTargetNot1 = pre.calculatePreStar(null, canNotReachTarget, absorbing);

		// complement probTargetNot1
		// S\Pre*(S\Pre*(target))
		BitSet result = new BitSet();
		result.set(0, dtmc.getNumStates(), true);
		result.andNot(probTargetNot1);

		// Finished precomputation
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Prob1");
		mainLog.println(" took " + timer / 1000.0 + " seconds.");

		return result;
	}

	/**
	 * Prob1 precomputation algorithm (using a fixed-point computation)
	 * i.e. determine the states of a DTMC which, with probability 1,
	 * reach a state in {@code target}, while remaining in those in {@code remain}.
	 * @param dtmc The DTMC
	 * @param remain Remain in these states (optional: {@code null} means "all")
	 * @param target Target states
	 */
	public BitSet prob1(DTMC dtmc, BitSet remain, BitSet target)
	{
		int n, iters;
		BitSet u, v, soln, unknown;
		boolean u_done, v_done;
		long timer;

		// Start precomputation
		timer = System.currentTimeMillis();
		mainLog.println("Starting Prob1...");

		// Special case: no target states
		if (target.cardinality() == 0) {
			return new BitSet(dtmc.getNumStates());
		}

		// Initialise vectors
		n = dtmc.getNumStates();
		u = new BitSet(n);
		v = new BitSet(n);
		soln = new BitSet(n);

		// Determine set of states actually need to perform computation for
		unknown = new BitSet();
		unknown.set(0, n);
		unknown.andNot(target);
		if (remain != null)
			unknown.and(remain);

		// Nested fixed point loop
		iters = 0;
		u_done = false;
		// Greatest fixed point
		u.set(0, n);
		while (!u_done) {
			v_done = false;
			// Least fixed point - should start from 0 but we optimise by
			// starting from 'target', thus bypassing first iteration
			v.clear();
			v.or(target);
			soln.clear();
			soln.or(target);
			while (!v_done) {
				iters++;
				// Single step of Prob1
				dtmc.prob1step(unknown, u, v, soln);
				// Check termination (inner)
				v_done = soln.equals(v);
				// v = soln
				v.clear();
				v.or(soln);
			}
			// Check termination (outer)
			u_done = v.equals(u);
			// u = v
			u.clear();
			u.or(v);
		}

		// Finished precomputation
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Prob1");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		return u;
	}

	/**
	 * Compute reachability probabilities using value iteration.
	 * @param dtmc The DTMC
	 * @param no Probability 0 states
	 * @param yes Probability 1 states
	 * @param init Optionally, an initial solution vector (will be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values.  
	 */
	protected ModelCheckerResult computeReachProbsValIter(DTMC dtmc, BitSet no, BitSet yes, double init[], BitSet known) throws PrismException
	{
		ModelCheckerResult res;
		BitSet unknown;
		int i, n, iters;
		double soln[], soln2[], tmpsoln[], initVal;
		boolean done;
		long timer;

		// Start value iteration
		timer = System.currentTimeMillis();
		mainLog.println("Starting value iteration...");

		// Store num states
		n = dtmc.getNumStates();

		// Create solution vector(s)
		soln = new double[n];
		soln2 = (init == null) ? new double[n] : init;

		// Initialise solution vectors. Use (where available) the following in order of preference:
		// (1) exact answer, if already known; (2) 1.0/0.0 if in yes/no; (3) passed in initial value; (4) initVal
		// where initVal is 0.0 or 1.0, depending on whether we converge from below/above. 
		initVal = (valIterDir == ValIterDir.BELOW) ? 0.0 : 1.0;
		if (init != null) {
			if (known != null) {
				for (i = 0; i < n; i++)
					soln[i] = soln2[i] = known.get(i) ? init[i] : yes.get(i) ? 1.0 : no.get(i) ? 0.0 : init[i];
			} else {
				for (i = 0; i < n; i++)
					soln[i] = soln2[i] = yes.get(i) ? 1.0 : no.get(i) ? 0.0 : init[i];
			}
		} else {
			for (i = 0; i < n; i++)
				soln[i] = soln2[i] = yes.get(i) ? 1.0 : no.get(i) ? 0.0 : initVal;
		}

		// Determine set of states actually need to compute values for
		unknown = new BitSet();
		unknown.set(0, n);
		unknown.andNot(yes);
		unknown.andNot(no);
		if (known != null)
			unknown.andNot(known);

		// Start iterations
		iters = 0;
		done = false;
		while (!done && iters < maxIters) {
			iters++;
			// Matrix-vector multiply
			dtmc.mvMult(soln, soln2, unknown, false);
			// Check termination
			done = PrismUtils.doublesAreClose(soln, soln2, termCritParam, termCrit == TermCrit.ABSOLUTE);
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished value iteration
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Value iteration");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		// Non-convergence is an error (usually)
		if (!done && errorOnNonConverge) {
			String msg = "Iterative method did not converge within " + iters + " iterations.";
			msg += "\nConsider using a different numerical method or increasing the maximum number of iterations";
			throw new PrismException(msg);
		}

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.numIters = iters;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Compute reachability probabilities using Gauss-Seidel.
	 * @param dtmc The DTMC
	 * @param no Probability 0 states
	 * @param yes Probability 1 states
	 * @param init Optionally, an initial solution vector (will be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values.  
	 */
	protected ModelCheckerResult computeReachProbsGaussSeidel(DTMC dtmc, BitSet no, BitSet yes, double init[], BitSet known) throws PrismException
	{
		ModelCheckerResult res;
		BitSet unknown;
		int i, n, iters;
		double soln[], initVal, maxDiff;
		boolean done;
		long timer;

		// Start value iteration
		timer = System.currentTimeMillis();
		mainLog.println("Starting Gauss-Seidel...");

		// Store num states
		n = dtmc.getNumStates();

		// Create solution vector
		soln = (init == null) ? new double[n] : init;

		// Initialise solution vector. Use (where available) the following in order of preference:
		// (1) exact answer, if already known; (2) 1.0/0.0 if in yes/no; (3) passed in initial value; (4) initVal
		// where initVal is 0.0 or 1.0, depending on whether we converge from below/above. 
		initVal = (valIterDir == ValIterDir.BELOW) ? 0.0 : 1.0;
		if (init != null) {
			if (known != null) {
				for (i = 0; i < n; i++)
					soln[i] = known.get(i) ? init[i] : yes.get(i) ? 1.0 : no.get(i) ? 0.0 : init[i];
			} else {
				for (i = 0; i < n; i++)
					soln[i] = yes.get(i) ? 1.0 : no.get(i) ? 0.0 : init[i];
			}
		} else {
			for (i = 0; i < n; i++)
				soln[i] = yes.get(i) ? 1.0 : no.get(i) ? 0.0 : initVal;
		}

		// Determine set of states actually need to compute values for
		unknown = new BitSet();
		unknown.set(0, n);
		unknown.andNot(yes);
		unknown.andNot(no);
		if (known != null)
			unknown.andNot(known);

		// Start iterations
		iters = 0;
		done = false;
		while (!done && iters < maxIters) {
			iters++;
			// Matrix-vector multiply
			maxDiff = dtmc.mvMultGS(soln, unknown, false, termCrit == TermCrit.ABSOLUTE);
			// Check termination
			done = maxDiff < termCritParam;
		}

		// Finished Gauss-Seidel
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Gauss-Seidel");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		// Non-convergence is an error (usually)
		if (!done && errorOnNonConverge) {
			String msg = "Iterative method did not converge within " + iters + " iterations.";
			msg += "\nConsider using a different numerical method or increasing the maximum number of iterations";
			throw new PrismException(msg);
		}

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.numIters = iters;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Compute arbitrary precision reachability probabilities using linear programming.
	 * @param dtmc The DTMC
	 * @param no Probability 0 states
	 * @param yes Probability 1 states
	 * @param init Optionally, an initial solution vector (will be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values.  
	 */
	protected ModelCheckerResult computeReachProbsExactLinearProg(DTMC dtmc, BitSet no, BitSet yes, double init[], BitSet known) throws PrismException
	{
		ModelCheckerResult res;
		BitSet unknown;
		int i, nStates, maybeSize, countMaybeTrans, ret;
		double sol, soln[], initVal, matAEntry, bEntry;
		long timer, matATimer, exactSolverTimer;
		SWIGTYPE_p_int ind;
		SWIGTYPE_p_double val;
		glp_smcp parm;
		glp_prob lp;

		// Start value iteration
		timer = System.currentTimeMillis();
		mainLog.println("Starting exact linear programming...");

		// Store num states
		nStates = dtmc.getNumStates();

		// Determine the set of maybe states (S?)
		unknown = new BitSet();
		unknown.set(0, nStates);
		unknown.andNot(yes);
		unknown.andNot(no);
		if (known != null)
			unknown.andNot(known);

		// Create solution vector
		soln = (init == null) ? new double[nStates] : init;

		// Initialise solution vector. Use (where available) the following in order of preference:
		// (1) exact answer, if already known; (2) 1.0/0.0 if in yes/no; (3) passed in initial value; (4) initVal
		// where initVal is 0.0 or 1.0, depending on whether we converge from below/above. 
		initVal = (valIterDir == ValIterDir.BELOW) ? 0.0 : 1.0;
		if (init != null) {
			if (known != null) {
				for (i = 0; i < nStates; i++)
					soln[i] = known.get(i) ? init[i] : yes.get(i) ? 1.0 : no.get(i) ? 0.0 : init[i];
			} else {
				for (i = 0; i < nStates; i++)
					soln[i] = yes.get(i) ? 1.0 : no.get(i) ? 0.0 : init[i];
			}
		} else {
			for (i = 0; i < nStates; i++)
				soln[i] = yes.get(i) ? 1.0 : no.get(i) ? 0.0 : initVal;
		}

		// Store the cardinality of the maybe state
		maybeSize = unknown.cardinality();

		// If we have states to compute values for
		if (maybeSize > 0) {
			// A mapping between maybe states and its positions in the maybe bitset.
			// This is useful for calculating the `A` matrix later on.
			// Also, calculate the number of the transitions of all maybe states `countMaybeTrans`
			countMaybeTrans = 0;
			HashMap<Integer,Integer> maybeToState = new HashMap<Integer,Integer>();
			HashMap<Integer,Integer> stateToMaybe = new HashMap<Integer,Integer>();
			int maybeStateCount = 1;
			for(int state = unknown.nextSetBit(0); state >= 0; state = unknown.nextSetBit(state + 1)) {
				maybeToState.put(maybeStateCount, state);
				stateToMaybe.put(state, maybeStateCount);
				countMaybeTrans++;
				maybeStateCount++;
			}

			// Memory allocation for index and value arrays.
			// For each transition, GLPK stores the values for each state in the maybe set
			// and uses these arrays as temporal storage
			ind = GLPK.new_intArray(maybeSize + 1);
			val = GLPK.new_doubleArray(maybeSize + 1);

			// Construct max (min) linear programming problem.
			// First, we put the problem in the canonical form
			// and then apply the duality definition
			lp = GLPK.glp_create_prob();
			mainLog.println("Linear programming problem created");

			// Set the lp constants for the dual simplex method.
			// columns -> one for each transition
			// rows -> maybe states
			GLPK.glp_add_cols(lp, countMaybeTrans);
			GLPK.glp_add_rows(lp, maybeSize);
			GLPK.intArray_setitem(ind, 0, 0);
			GLPK.doubleArray_setitem(val, 0, 0);

			// Constraints for each equation expressed as inequalities.
			// For the min (max) problem, each equation has -1 as a upper (lower) bound and we compute the max (min).
			// This was obtained rewriting the problems (6) (7) in their canonical form, and then construct the dual.
			// The `-1` bounds correspond to the values of the cost vector (remember that we put the problems
			// in canonical form first).
			// Also, we set each row (representing a maybe state) as part of the basis defined in (10)
			for (int row = 1; row <= maybeSize; row++) {
				// The name of the state
				GLPK.glp_set_row_name(lp, row, "s" + unknown.nextSetBit(row));
				GLPK.glp_set_row_bnds(lp, row, GLPKConstants.GLP_UP, 0, -1);
				GLPK.glp_set_obj_dir(lp, GLPKConstants.GLP_MAX);
				GLPK.glp_set_row_stat(lp, row, GLPKConstants.GLP_BS);
				GLPK.intArray_setitem(ind, row, 0);
				GLPK.doubleArray_setitem(val, row, 0);
			}

			// The current column of the matrix (transition)
			int currentTransition = 1;
			matATimer = System.currentTimeMillis();
			// Fill out the (A | I) matrix (lp problem equations) of the reachability problem.
			// In this step, we calculate the values for each entry of the A matrix,
			// going through all maybe states and their transitions for each choice
			for (int state = unknown.nextSetBit(0); state >= 0; state = unknown.nextSetBit(state + 1)) {
				// Index of the i-th equation in the lp's matrix
				int eqIndex = 1;
				Iterator<Map.Entry<Integer, Double>> iter = dtmc.getTransitionsIterator(state);
				bEntry = 0.;
				boolean pointsToItself = false;
				// Iterate over the transitions between st and choice
				while (iter.hasNext()) {
					matAEntry = 0.;
					Map.Entry<Integer, Double> entry = iter.next();
					int actualKey = entry.getKey();
					// Skip if the probability is 0
					if (entry.getValue() == 0)
						continue;
					// Calculate the entries (summation) for the b vector (constraint vector)
					if (yes.get(actualKey))
						bEntry += entry.getValue();
					// If it is a maybe state, we calculate the matrix entry as defined on
					// page 8 of the paper
					if (unknown.get(actualKey)) {
						if (actualKey == state) {
							pointsToItself = true;
							matAEntry = entry.getValue() - 1;
						} else {
							matAEntry = entry.getValue();
						}
						// Write the entry of each equation in the array
						GLPK.intArray_setitem(ind, eqIndex, stateToMaybe.get(actualKey));
						GLPK.doubleArray_setitem(val, eqIndex, matAEntry);
						eqIndex++;
					}
				}
				// If the state does not point to itself, then fill out the missing entry
				if (!pointsToItself) {
					GLPK.intArray_setitem(ind, eqIndex, stateToMaybe.get(state));
					GLPK.doubleArray_setitem(val, eqIndex, -1);
					eqIndex++;
				}

				// Set the values of the arrays in the full linear programming equation matrix.
				// Negate the summation calculated for the constraint vector entries
				GLPK.glp_set_col_bnds(lp, currentTransition, GLPKConstants.GLP_LO, 0, 0);
				GLPK.glp_set_mat_col(lp, currentTransition, eqIndex - 1, ind, val);
				GLPK.glp_set_obj_coef(lp, currentTransition, -bEntry);

				currentTransition++;
			}
			mainLog.println("Linear programming equations construction time: " +
					((double)System.currentTimeMillis() - matATimer)/1000 + " seconds");

			// Solving the linear problem in the linear programming library GLPK.
			// probs[]: an array for storing the exact probabilities as string in the form `p/q`
			// `num` and `den` store the temporal `p` and `q` respectively (this could be avoided)
			String probs[] = new String[nStates];

			// Set up exact parameters
			parm = new glp_smcp();
			GLPK.glp_init_smcp(parm);
			parm.setPrecision(this.getPrecision());
			parm.setNum_states(nStates);

			// Solve lp problem
			exactSolverTimer = System.currentTimeMillis();
			ret = GLPK.glp_exact(lp, parm);

			// Check return value: if `ret` is not zero there has been an error
			if (ret != 0) {
				String msg;
				if (ret == GLPKConstants.GLP_EBADB) {
					msg = "The initial basis specified in the problem object is invalid: wrong number of basic variables";
				} else if (ret == GLPKConstants.GLP_ESING) {
					msg = "The basis matrix corresponding to the initial basis is singular";
				} else if (ret == GLPKConstants.GLP_EBOUND) {
					msg = "Some double-bounded variables have incorrect bound";
				} else {
					msg = "The linear programming problem could not be solved";
				}
				mainLog.println(msg);
				throw new PrismException(msg);
			}

			// Calculate and store exact probabilities.
			// For each maybe state, we extract the fixed precision results from GLPK and store them in `probs[]`.
			// `sol` stores the exact values as doubles. That implies that the precision is at most 64-bit
			// However, the exact value is expressed as a string in `probs[]`.
			sol = GLPK.glp_get_obj_val(lp);
			String currentResult;
			int exp;
			mainLog.println("\n" + this.getPrecision() + "-bit results (non-zero only) for each state of the DTMC:");
			for (int dtmcState = 0; dtmcState < nStates; dtmcState++) {
				if (unknown.get(dtmcState)) {
					sol = GLPK.glp_get_row_dual(lp, stateToMaybe.get(dtmcState));
					soln[dtmcState] = sol;
					currentResult = GLPK.uint8Array_toString(GLPK.uint8ArrayArray_getitem(GLPK.glp_get_probs(lp), stateToMaybe.get(dtmcState) - 1));
					exp = GLPK.intArray_getitem(GLPK.glp_get_exps(lp), stateToMaybe.get(dtmcState) - 1);
					// We need to format the output since we get the exponent as a position in the string
					String zeroes = "";
					for (int nZero = 0; nZero < Math.abs(exp); nZero++)
						zeroes += "0";
					currentResult = exp > 0 ? new StringBuilder(currentResult).insert(exp, ".").toString() : "0." + zeroes + currentResult;
					probs[dtmcState] = currentResult; 
				}
				// If it is a `yes` state, its probability is 1
				else if (yes.get(dtmcState)) {
					soln[dtmcState] = 1.;
					probs[dtmcState] = "1";
				}
				// If it is a `no` state, its probability is 0
				else if (no.get(dtmcState)) {
					soln[dtmcState] = 0.;
					probs[dtmcState] = "0";
				}
				// Avoid zero entries
				if (probs[dtmcState] != "0")
					mainLog.println("[" + dtmcState + "]: " + probs[dtmcState]);
			}
			mainLog.println("\nExact probabilities calculation time: " +
					((double)System.currentTimeMillis() - exactSolverTimer)/1000 + " seconds");

			// Free memory
			GLPK.delete_intArray(ind);
			GLPK.delete_doubleArray(val);
			GLPK.delete_intArray(GLPK.glp_get_exps(lp));
			GLPK.delete_uint8ArrayArray(GLPK.glp_get_probs(lp));
			GLPK.delete_uint8ArrayArray(GLPK.glp_get_nums(lp));
			GLPK.delete_uint8ArrayArray(GLPK.glp_get_dens(lp));
			GLPK.glp_delete_prob(lp);

		}

		// Finished linear programming
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Exact linear programming");
		mainLog.println(" took " + timer / 1000.0 + " seconds.");

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Compute bounded reachability probabilities.
	 * i.e. compute the probability of reaching a state in {@code target} within k steps.
	 * @param dtmc The DTMC
	 * @param target Target states
	 * @param k Bound
	 */
	public ModelCheckerResult computeBoundedReachProbs(DTMC dtmc, BitSet target, int k) throws PrismException
	{
		return computeBoundedReachProbs(dtmc, null, target, k, null, null);
	}

	/**
	 * Compute bounded until probabilities.
	 * i.e. compute the probability of reaching a state in {@code target},
	 * within k steps, and while remaining in states in {@code remain}.
	 * @param dtmc The DTMC
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param k Bound
	 */
	public ModelCheckerResult computeBoundedUntilProbs(DTMC dtmc, BitSet remain, BitSet target, int k) throws PrismException
	{
		return computeBoundedReachProbs(dtmc, remain, target, k, null, null);
	}

	/**
	 * Compute bounded reachability/until probabilities.
	 * i.e. compute the probability of reaching a state in {@code target},
	 * within k steps, and while remaining in states in {@code remain}.
	 * @param dtmc The DTMC
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param k Bound
	 * @param init Initial solution vector - pass null for default
	 * @param results Optional array of size b+1 to store (init state) results for each step (null if unused)
	 */
	public ModelCheckerResult computeBoundedReachProbs(DTMC dtmc, BitSet remain, BitSet target, int k, double init[], double results[]) throws PrismException
	{
		ModelCheckerResult res = null;
		BitSet unknown;
		int i, n, iters;
		double soln[], soln2[], tmpsoln[];
		long timer;

		// Start bounded probabilistic reachability
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting bounded probabilistic reachability...");

		// Store num states
		n = dtmc.getNumStates();

		// Create solution vector(s)
		soln = new double[n];
		soln2 = (init == null) ? new double[n] : init;

		// Initialise solution vectors. Use passed in initial vector, if present
		if (init != null) {
			for (i = 0; i < n; i++)
				soln[i] = soln2[i] = target.get(i) ? 1.0 : init[i];
		} else {
			for (i = 0; i < n; i++)
				soln[i] = soln2[i] = target.get(i) ? 1.0 : 0.0;
		}
		// Store intermediate results if required
		// (compute min/max value over initial states for first step)
		if (results != null) {
			// TODO: whether this is min or max should be specified somehow
			results[0] = Utils.minMaxOverArraySubset(soln2, dtmc.getInitialStates(), true);
		}

		// Determine set of states actually need to perform computation for
		unknown = new BitSet();
		unknown.set(0, n);
		unknown.andNot(target);
		if (remain != null)
			unknown.and(remain);

		// Start iterations
		iters = 0;
		while (iters < k) {

			iters++;
			// Matrix-vector multiply
			dtmc.mvMult(soln, soln2, unknown, false);
			// Store intermediate results if required
			// (compute min/max value over initial states for this step)
			if (results != null) {
				// TODO: whether this is min or max should be specified somehow
				results[iters] = Utils.minMaxOverArraySubset(soln2, dtmc.getInitialStates(), true);
			}
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished bounded probabilistic reachability
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Bounded probabilistic reachability");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.lastSoln = soln2;
		res.numIters = iters;
		res.timeTaken = timer / 1000.0;
		res.timePre = 0.0;
		return res;
	}

	/**
	 * Compute expected reachability rewards.
	 * @param dtmc The DTMC
	 * @param mcRewards The rewards
	 * @param target Target states
	 */
	public ModelCheckerResult computeReachRewards(DTMC dtmc, MCRewards mcRewards, BitSet target) throws PrismException
	{
		return computeReachRewards(dtmc, mcRewards, target, null, null);
	}

	/**
	 * Compute expected reachability rewards.
	 * @param dtmc The DTMC
	 * @param mcRewards The rewards
	 * @param target Target states
	 * @param init Optionally, an initial solution vector (may be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values.  
	 */
	public ModelCheckerResult computeReachRewards(DTMC dtmc, MCRewards mcRewards, BitSet target, double init[], BitSet known) throws PrismException
	{
		ModelCheckerResult res = null;
		BitSet inf;
		int n, numTarget, numInf;
		long timer, timerProb1;
		// Local copy of setting
		LinEqMethod linEqMethod = this.linEqMethod;

		// Switch to a supported method, if necessary
		if (!(linEqMethod == LinEqMethod.POWER)) {
			linEqMethod = LinEqMethod.POWER;
			mainLog.printWarning("Switching to linear equation solution method \"" + linEqMethod.fullName() + "\"");
		}

		// Start expected reachability
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting expected reachability...");

		// Check for deadlocks in non-target state (because breaks e.g. prob1)
		dtmc.checkForDeadlocks(target);

		// Store num states
		n = dtmc.getNumStates();

		// Optimise by enlarging target set (if more info is available)
		if (init != null && known != null && !known.isEmpty()) {
			BitSet targetNew = (BitSet) target.clone();
			for (int i : new IterableBitSet(known)) {
				if (init[i] == 1.0) {
					targetNew.set(i);
				}
			}
			target = targetNew;
		}

		// Precomputation (not optional)
		timerProb1 = System.currentTimeMillis();
		if (preRel) {
			// prob1 via predecessor relation
			PredecessorRelation pre = dtmc.getPredecessorRelation(this, true);
			inf = prob1(dtmc, null, target, pre);
		} else {
			// prob1 via fixed-point algorithm
			inf = prob1(dtmc, null, target);
		}
		inf.flip(0, n);
		timerProb1 = System.currentTimeMillis() - timerProb1;

		// Print results of precomputation
		numTarget = target.cardinality();
		numInf = inf.cardinality();
		mainLog.println("target=" + numTarget + ", inf=" + numInf + ", rest=" + (n - (numTarget + numInf)));

		// Compute rewards
		switch (linEqMethod) {
		case POWER:
			res = computeReachRewardsValIter(dtmc, mcRewards, target, inf, init, known);
			break;
		default:
			throw new PrismException("Unknown linear equation solution method " + linEqMethod.fullName());
		}

		// Finished expected reachability
		timer = System.currentTimeMillis() - timer;
		mainLog.println("Expected reachability took " + timer / 1000.0 + " seconds.");

		// Update time taken
		res.timeTaken = timer / 1000.0;
		res.timePre = timerProb1 / 1000.0;

		return res;
	}

	/**
	 * Compute expected reachability rewards using value iteration.
	 * @param dtmc The DTMC
	 * @param mcRewards The rewards
	 * @param target Target states
	 * @param inf States for which reward is infinite
	 * @param init Optionally, an initial solution vector (will be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values.
	 */
	protected ModelCheckerResult computeReachRewardsValIter(DTMC dtmc, MCRewards mcRewards, BitSet target, BitSet inf, double init[], BitSet known)
			throws PrismException
	{
		ModelCheckerResult res;
		BitSet unknown;
		int i, n, iters;
		double soln[], soln2[], tmpsoln[];
		boolean done;
		long timer;

		// Start value iteration
		timer = System.currentTimeMillis();
		mainLog.println("Starting value iteration...");

		// Store num states
		n = dtmc.getNumStates();

		// Create solution vector(s)
		soln = new double[n];
		soln2 = (init == null) ? new double[n] : init;

		// Initialise solution vectors. Use (where available) the following in order of preference:
		// (1) exact answer, if already known; (2) 0.0/infinity if in target/inf; (3) passed in initial value; (4) 0.0
		if (init != null) {
			if (known != null) {
				for (i = 0; i < n; i++)
					soln[i] = soln2[i] = known.get(i) ? init[i] : target.get(i) ? 0.0 : inf.get(i) ? Double.POSITIVE_INFINITY : init[i];
			} else {
				for (i = 0; i < n; i++)
					soln[i] = soln2[i] = target.get(i) ? 0.0 : inf.get(i) ? Double.POSITIVE_INFINITY : init[i];
			}
		} else {
			for (i = 0; i < n; i++)
				soln[i] = soln2[i] = target.get(i) ? 0.0 : inf.get(i) ? Double.POSITIVE_INFINITY : 0.0;
		}

		// Determine set of states actually need to compute values for
		unknown = new BitSet();
		unknown.set(0, n);
		unknown.andNot(target);
		unknown.andNot(inf);
		if (known != null)
			unknown.andNot(known);

		// Start iterations
		iters = 0;
		done = false;
		while (!done && iters < maxIters) {
			//mainLog.println(soln);
			iters++;
			// Matrix-vector multiply
			dtmc.mvMultRew(soln, mcRewards, soln2, unknown, false);
			// Check termination
			done = PrismUtils.doublesAreClose(soln, soln2, termCritParam, termCrit == TermCrit.ABSOLUTE);
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished value iteration
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Value iteration");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		// Non-convergence is an error (usually)
		if (!done && errorOnNonConverge) {
			String msg = "Iterative method did not converge within " + iters + " iterations.";
			msg += "\nConsider using a different numerical method or increasing the maximum number of iterations";
			throw new PrismException(msg);
		}

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.numIters = iters;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Compute (forwards) steady-state probabilities
	 * i.e. compute the long-run probability of being in each state,
	 * assuming the initial distribution {@code initDist}. 
	 * For space efficiency, the initial distribution vector will be modified and values over-written,  
	 * so if you wanted it, take a copy. 
	 * @param dtmc The DTMC
	 * @param initDist Initial distribution (will be overwritten)
	 */
	public ModelCheckerResult computeSteadyStateProbs(DTMC dtmc, double initDist[]) throws PrismException
	{
		ModelCheckerResult res;
		BitSet startNot, bscc;
		double probBSCCs[], solnProbs[], reachProbs[];
		int n, numBSCCs = 0, allInOneBSCC;
		long timer;

		timer = System.currentTimeMillis();

		// Store num states
		n = dtmc.getNumStates();
		// Create results vector
		solnProbs = new double[n];

		// Compute bottom strongly connected components (BSCCs)
		SCCComputer sccComputer = SCCComputer.createSCCComputer(this, dtmc);
		sccComputer.computeBSCCs();
		List<BitSet> bsccs = sccComputer.getBSCCs();
		BitSet notInBSCCs = sccComputer.getNotInBSCCs();
		numBSCCs = bsccs.size();

		// See which states in the initial distribution do *not* have non-zero prob
		startNot = new BitSet();
		for (int i = 0; i < n; i++) {
			if (initDist[i] == 0)
				startNot.set(i);
		}
		// Determine whether initial states are all in a single BSCC 
		allInOneBSCC = -1;
		for (int b = 0; b < numBSCCs; b++) {
			if (!bsccs.get(b).intersects(startNot)) {
				allInOneBSCC = b;
				break;
			}
		}

		// If all initial states are in a single BSCC, it's easy...
		// Just compute steady-state probabilities for the BSCC
		if (allInOneBSCC != -1) {
			mainLog.println("\nInitial states all in one BSCC (so no reachability probabilities computed)");
			bscc = bsccs.get(allInOneBSCC);
			computeSteadyStateProbsForBSCC(dtmc, bscc, solnProbs);
		}

		// Otherwise, have to consider all the BSCCs
		else {

			// Compute probability of reaching each BSCC from initial distribution 
			probBSCCs = new double[numBSCCs];
			for (int b = 0; b < numBSCCs; b++) {
				mainLog.println("\nComputing probability of reaching BSCC " + (b + 1));
				bscc = bsccs.get(b);
				// Compute probabilities
				reachProbs = computeUntilProbs(dtmc, notInBSCCs, bscc).soln;
				// Compute probability of reaching BSCC, which is dot product of
				// vectors for initial distribution and probabilities of reaching it
				probBSCCs[b] = 0.0;
				for (int i = 0; i < n; i++) {
					probBSCCs[b] += initDist[i] * reachProbs[i];
				}
				mainLog.print("\nProbability of reaching BSCC " + (b + 1) + ": " + probBSCCs[b] + "\n");
			}

			// Compute steady-state probabilities for each BSCC 
			for (int b = 0; b < numBSCCs; b++) {
				mainLog.println("\nComputing steady-state probabilities for BSCC " + (b + 1));
				bscc = bsccs.get(b);
				// Compute steady-state probabilities for the BSCC
				computeSteadyStateProbsForBSCC(dtmc, bscc, solnProbs);
				// Multiply by BSCC reach prob
				for (int i = bscc.nextSetBit(0); i >= 0; i = bscc.nextSetBit(i + 1))
					solnProbs[i] *= probBSCCs[b];
			}
		}

		// Return results
		res = new ModelCheckerResult();
		res.soln = solnProbs;
		timer = System.currentTimeMillis() - timer;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Perform (backwards) steady-state probabilities, as required for (e.g. CSL) model checking.
	 * Compute, for each initial state s, the sum over all states s'
	 * of the steady-state probability of being in s'
	 * multiplied by the corresponding probability in the vector {@code multProbs}.
	 * If {@code multProbs} is null, it is assumed to be all 1s.
	 * @param dtmc The DTMC
	 * @param multProbs Multiplication vector (optional: null means all 1s)
	 */
	public ModelCheckerResult computeSteadyStateBackwardsProbs(DTMC dtmc, double multProbs[]) throws PrismException
	{
		ModelCheckerResult res;
		BitSet bscc;
		double probBSCCs[], ssProbs[], reachProbs[], soln[];
		int n, numBSCCs = 0;
		long timer;

		timer = System.currentTimeMillis();

		// Store num states
		n = dtmc.getNumStates();

		// Compute bottom strongly connected components (BSCCs)
		SCCComputer sccComputer = SCCComputer.createSCCComputer(this, dtmc);
		sccComputer.computeBSCCs();
		List<BitSet> bsccs = sccComputer.getBSCCs();
		BitSet notInBSCCs = sccComputer.getNotInBSCCs();
		numBSCCs = bsccs.size();

		// Compute steady-state probability for each BSCC...
		probBSCCs = new double[numBSCCs];
		ssProbs = new double[n];
		for (int b = 0; b < numBSCCs; b++) {
			mainLog.println("\nComputing steady state probabilities for BSCC " + (b + 1));
			bscc = bsccs.get(b);
			// Compute steady-state probabilities for the BSCC
			computeSteadyStateProbsForBSCC(dtmc, bscc, ssProbs);
			// Compute weighted sum of probabilities with multProbs
			probBSCCs[b] = 0.0;
			if (multProbs == null) {
				for (int i = bscc.nextSetBit(0); i >= 0; i = bscc.nextSetBit(i + 1)) {
					probBSCCs[b] += ssProbs[i];
				}
			} else {
				for (int i = bscc.nextSetBit(0); i >= 0; i = bscc.nextSetBit(i + 1)) {
					probBSCCs[b] += multProbs[i] * ssProbs[i];
				}
			}
			mainLog.print("\nValue for BSCC " + (b + 1) + ": " + probBSCCs[b] + "\n");
		}

		// Create/initialise prob vector
		soln = new double[n];
		for (int i = 0; i < n; i++) {
			soln[i] = 0.0;
		}

		// If every state is in a BSCC, it's much easier...
		if (notInBSCCs.isEmpty()) {
			mainLog.println("\nAll states are in BSCCs (so no reachability probabilities computed)");
			for (int b = 0; b < numBSCCs; b++) {
				bscc = bsccs.get(b);
				for (int i = bscc.nextSetBit(0); i >= 0; i = bscc.nextSetBit(i + 1))
					soln[i] += probBSCCs[b];
			}
		}

		// Otherwise we have to do more work...
		else {
			// Compute probabilities of reaching each BSCC...
			for (int b = 0; b < numBSCCs; b++) {
				// Skip BSCCs with zero probability
				if (probBSCCs[b] == 0.0)
					continue;
				mainLog.println("\nComputing probabilities of reaching BSCC " + (b + 1));
				bscc = bsccs.get(b);
				// Compute probabilities
				reachProbs = computeUntilProbs(dtmc, notInBSCCs, bscc).soln;
				// Multiply by value for BSCC, add to total
				for (int i = 0; i < n; i++) {
					soln[i] += reachProbs[i] * probBSCCs[b];
				}
			}
		}

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		timer = System.currentTimeMillis() - timer;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Compute steady-state probabilities for a BSCC
	 * i.e. compute the long-run probability of being in each state of the BSCC.
	 * No initial distribution is specified since it does not affect the result.
	 * The result will be stored in the relevant portion of a full vector,
	 * whose size equals the number of states in the DTMC.
	 * Optionally, pass in an existing vector to be used for this purpose.
	 * @param dtmc The DTMC
	 * @param bscc The BSCC to be analysed
	 * @param result Storage for result (ignored if null)
	 */
	public ModelCheckerResult computeSteadyStateProbsForBSCC(DTMC dtmc, BitSet bscc, double result[]) throws PrismException
	{
		ModelCheckerResult res;
		int n, iters;
		double soln[], soln2[], tmpsoln[];
		boolean done;
		long timer;

		// Start value iteration
		timer = System.currentTimeMillis();
		mainLog.println("Starting value iteration...");

		// Store num states
		n = dtmc.getNumStates();

		// Create solution vector(s)
		// Use the passed in vector, if present
		soln = result == null ? new double[n] : result;
		soln2 = new double[n];

		// Initialise solution vectors. Equiprobable for BSCC states.
		double equiprob = 1.0 / bscc.cardinality();
		for (int i = bscc.nextSetBit(0); i >= 0; i = bscc.nextSetBit(i + 1))
			soln[i] = soln2[i] = equiprob;

		// Start iterations
		iters = 0;
		done = false;
		while (!done && iters < maxIters) {
			iters++;
			// Matrix-vector multiply
			dtmc.vmMult(soln, soln2);
			// Check termination
			done = PrismUtils.doublesAreClose(soln, soln2, termCritParam, termCrit == TermCrit.ABSOLUTE);
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished value iteration
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Value iteration");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		// Non-convergence is an error (usually)
		if (!done && errorOnNonConverge) {
			String msg = "Iterative method did not converge within " + iters + " iterations.";
			msg += "\nConsider using a different numerical method or increasing the maximum number of iterations";
			throw new PrismException(msg);
		}

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.numIters = iters;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Compute transient probabilities
	 * i.e. compute the probability of being in each state at time step {@code k},
	 * assuming the initial distribution {@code initDist}. 
	 * For space efficiency, the initial distribution vector will be modified and values over-written,  
	 * so if you wanted it, take a copy. 
	 * @param dtmc The DTMC
	 * @param k Time step
	 * @param initDist Initial distribution (will be overwritten)
	 */
	public ModelCheckerResult computeTransientProbs(DTMC dtmc, int k, double initDist[]) throws PrismException
	{
		ModelCheckerResult res;
		int n, iters;
		double soln[], soln2[], tmpsoln[];
		long timer;

		// Start transient probability computation
		timer = System.currentTimeMillis();
		mainLog.println("Starting transient probability computation...");

		// Store num states
		n = dtmc.getNumStates();

		// Create solution vector(s)
		// Use the passed in vector, if present
		soln = initDist;
		soln2 = new double[n];

		// Start iterations
		for (iters = 0; iters < k; iters++) {
			// Matrix-vector multiply
			dtmc.vmMult(soln, soln2);
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished transient probability computation
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Transient probability computation");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.numIters = iters;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Simple test program.
	 */
	public static void main(String args[])
	{
		DTMCModelChecker mc;
		DTMCSimple dtmc;
		ModelCheckerResult res;
		try {
			// Two examples of building and solving a DTMC

			int version = 2;
			if (version == 1) {

				// 1. Read in from .tra and .lab files
				//    Run as: PRISM_MAINCLASS=explicit.DTMCModelChecker bin/prism dtmc.tra dtmc.lab target_label
				mc = new DTMCModelChecker(null);
				dtmc = new DTMCSimple();
				dtmc.buildFromPrismExplicit(args[0]);
				dtmc.addInitialState(0);
				//System.out.println(dtmc);
				Map<String, BitSet> labels = StateModelChecker.loadLabelsFile(args[1]);
				//System.out.println(labels);
				BitSet target = labels.get(args[2]);
				if (target == null)
					throw new PrismException("Unknown label \"" + args[2] + "\"");
				for (int i = 3; i < args.length; i++) {
					if (args[i].equals("-nopre"))
						mc.setPrecomp(false);
				}
				res = mc.computeReachProbs(dtmc, target);
				System.out.println(res.soln[0]);

			} else {

				// 2. Build DTMC directly
				//    Run as: PRISM_MAINCLASS=explicit.DTMCModelChecker bin/prism
				//    (example taken from p.14 of Lec 5 of http://www.prismmodelchecker.org/lectures/pmc/) 
				mc = new DTMCModelChecker(null);
				dtmc = new DTMCSimple(6);
				dtmc.setProbability(0, 1, 0.1);
				dtmc.setProbability(0, 2, 0.9);
				dtmc.setProbability(1, 0, 0.4);
				dtmc.setProbability(1, 3, 0.6);
				dtmc.setProbability(2, 2, 0.1);
				dtmc.setProbability(2, 3, 0.1);
				dtmc.setProbability(2, 4, 0.5);
				dtmc.setProbability(2, 5, 0.3);
				dtmc.setProbability(3, 3, 1.0);
				dtmc.setProbability(4, 4, 1.0);
				dtmc.setProbability(5, 5, 0.3);
				dtmc.setProbability(5, 4, 0.7);
				System.out.println(dtmc);
				BitSet target = new BitSet();
				target.set(4);
				BitSet remain = new BitSet();
				remain.set(1);
				remain.flip(0, 6);
				System.out.println(target);
				System.out.println(remain);
				res = mc.computeUntilProbs(dtmc, remain, target);
				System.out.println(res.soln[0]);
			}
		} catch (PrismException e) {
			System.out.println(e);
		}
	}
}
