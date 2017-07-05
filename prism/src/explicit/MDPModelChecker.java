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

import java.util.Arrays;
import java.util.BitSet;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import parser.VarList;
import parser.ast.Declaration;
import parser.ast.DeclarationIntUnbounded;
import parser.ast.Expression;
import prism.Prism;
import prism.PrismComponent;
import prism.PrismDevNullLog;
import prism.PrismException;
import prism.PrismFileLog;
import prism.PrismLog;
import prism.PrismSettings;
import prism.PrismUtils;
import strat.MDStrategyArray;
import acceptance.AcceptanceReach;
import acceptance.AcceptanceType;
import common.IterableBitSet;
import explicit.rewards.MCRewards;
import explicit.rewards.MCRewardsFromMDPRewards;
import explicit.rewards.MDPRewards;
import explicit.rewards.Rewards;

import org.gnu.glpk.GLPK;
import org.gnu.glpk.GLPKConstants;
import org.gnu.glpk.SWIGTYPE_p_double;
import org.gnu.glpk.SWIGTYPE_p_int;
import org.gnu.glpk.glp_prob;
import org.gnu.glpk.glp_smcp;

/**
 * Explicit-state model checker for Markov decision processes (MDPs).
 */
public class MDPModelChecker extends ProbModelChecker
{
	/**
	 * Create a new MDPModelChecker, inherit basic state from parent (unless null).
	 */
	public MDPModelChecker(PrismComponent parent) throws PrismException
	{
		super(parent);
	}
	
	// Model checking functions

	@Override
	protected StateValues checkProbPathFormulaLTL(Model model, Expression expr, boolean qual, MinMax minMax, BitSet statesOfInterest) throws PrismException
	{
		LTLModelChecker mcLtl;
		StateValues probsProduct, probs;
		MDPModelChecker mcProduct;
		LTLModelChecker.LTLProduct<MDP> product;

		// For min probabilities, need to negate the formula
		// (add parentheses to allow re-parsing if required)
		if (minMax.isMin()) {
			expr = Expression.Not(Expression.Parenth(expr.deepCopy()));
		}

		// For LTL model checking routines
		mcLtl = new LTLModelChecker(this);

		// Build product of MDP and automaton
		AcceptanceType[] allowedAcceptance = {
				AcceptanceType.BUCHI,
				AcceptanceType.RABIN,
				AcceptanceType.GENERALIZED_RABIN,
				AcceptanceType.REACH
		};
		product = mcLtl.constructProductMDP(this, (MDP)model, expr, statesOfInterest, allowedAcceptance);
		
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
			mainLog.println("\nSkipping accepting MEC computation since acceptance is defined via goal states...");
			acc = ((AcceptanceReach)product.getAcceptance()).getGoalStates();
		} else {
			mainLog.println("\nFinding accepting MECs...");
			acc = mcLtl.findAcceptingECStates(product.getProductModel(), product.getAcceptance());
		}
		mainLog.println("\nComputing reachability probabilities...");
		mcProduct = new MDPModelChecker(this);
		mcProduct.inheritSettings(this);
		ModelCheckerResult res = mcProduct.computeReachProbs((MDP) product.getProductModel(), acc, false);
		probsProduct = StateValues.createFromDoubleArray(res.soln, product.getProductModel());

		// Subtract from 1 if we're model checking a negated formula for regular Pmin
		if (minMax.isMin()) {
			probsProduct.timesConstant(-1.0);
			probsProduct.plusConstant(1.0);
		}

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
		MDPRewards productRewards;
		StateValues rewardsProduct, rewards;
		MDPModelChecker mcProduct;
		LTLModelChecker.LTLProduct<MDP> product;

		// For LTL model checking routines
		mcLtl = new LTLModelChecker(this);

		// Build product of MDP and automaton
		AcceptanceType[] allowedAcceptance = {
				AcceptanceType.RABIN,
				AcceptanceType.REACH
		};
		product = mcLtl.constructProductMDP(this, (MDP)model, expr, statesOfInterest, allowedAcceptance);
		
		// Adapt reward info to product model
		productRewards = ((MDPRewards) modelRewards).liftFromModel(product);
		
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
			// For a DFA, just collect the accept states
			mainLog.println("\nSkipping end component detection since DRA is a DFA...");
			acc = ((AcceptanceReach)product.getAcceptance()).getGoalStates();
		} else {
			// Usually, we have to detect end components in the product
			mainLog.println("\nFinding accepting end components...");
			acc = mcLtl.findAcceptingECStates(product.getProductModel(), product.getAcceptance());
		}
		mainLog.println("\nComputing reachability rewards...");
		mcProduct = new MDPModelChecker(this);
		mcProduct.inheritSettings(this);
		ModelCheckerResult res = mcProduct.computeReachRewards(product.getProductModel(), productRewards, acc, minMax.isMin());
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
	
	// Numerical computation functions

	/**
	 * Compute next=state probabilities.
	 * i.e. compute the probability of being in a state in {@code target} in the next step.
	 * @param mdp The MDP
	 * @param target Target states
	 * @param min Min or max probabilities (true=min, false=max)
	 */
	public ModelCheckerResult computeNextProbs(MDP mdp, BitSet target, boolean min) throws PrismException
	{
		ModelCheckerResult res = null;
		int n;
		double soln[], soln2[];
		long timer;

		timer = System.currentTimeMillis();

		// Store num states
		n = mdp.getNumStates();

		// Create/initialise solution vector(s)
		soln = Utils.bitsetToDoubleArray(target, n);
		soln2 = new double[n];

		// Next-step probabilities 
		mdp.mvMultMinMax(soln, min, soln2, null, false, null);

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln2;
		res.numIters = 1;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Given a value vector x, compute the probability:
	 *   v(s) = min/max sched [ Sum_s' P_sched(s,s')*x(s') ]  for s labeled with a,
	 *   v(s) = 0   for s not labeled with a.
	 *
	 * Clears the StateValues object x.
	 *
	 * @param tr the transition matrix
	 * @param a the set of states labeled with a
	 * @param x the value vector
	 * @param min compute min instead of max
	 */
	public double[] computeRestrictedNext(MDP mdp, BitSet a, double[] x, boolean min)
	{
		int n;
		double soln[];

		// Store num states
		n = mdp.getNumStates();

		// initialized to 0.0
		soln = new double[n];

		// Next-step probabilities multiplication
		// restricted to a states
		mdp.mvMultMinMax(x, min, soln, a, false, null);

		return soln;
	}

	/**
	 * Compute reachability probabilities.
	 * i.e. compute the min/max probability of reaching a state in {@code target}.
	 * @param mdp The MDP
	 * @param target Target states
	 * @param min Min or max probabilities (true=min, false=max)
	 */
	public ModelCheckerResult computeReachProbs(MDP mdp, BitSet target, boolean min) throws PrismException
	{
		return computeReachProbs(mdp, null, target, min, null, null);
	}

	/**
	 * Compute until probabilities.
	 * i.e. compute the min/max probability of reaching a state in {@code target},
	 * while remaining in those in {@code remain}.
	 * @param mdp The MDP
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param min Min or max probabilities (true=min, false=max)
	 */
	public ModelCheckerResult computeUntilProbs(MDP mdp, BitSet remain, BitSet target, boolean min) throws PrismException
	{
		return computeReachProbs(mdp, remain, target, min, null, null);
	}

	/**
	 * Compute reachability/until probabilities.
	 * i.e. compute the min/max probability of reaching a state in {@code target},
	 * while remaining in those in {@code remain}.
	 * @param mdp The MDP
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param min Min or max probabilities (true=min, false=max)
	 * @param init Optionally, an initial solution vector (may be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values).
	 * Also, 'known' values cannot be passed for some solution methods, e.g. policy iteration.  
	 */
	public ModelCheckerResult computeReachProbs(MDP mdp, BitSet remain, BitSet target, boolean min, double init[], BitSet known) throws PrismException
	{
		ModelCheckerResult res = null;
		BitSet no, yes;
		int n, numYes, numNo;
		long timer, timerProb0, timerProb1;
		int strat[] = null;
		// Local copy of setting
		MDPSolnMethod mdpSolnMethod = this.mdpSolnMethod;

		// Switch to a supported method, if necessary
		if (GLPK.EXACTLP_REQUIREMENTS == 0) {
			mdpSolnMethod = MDPSolnMethod.GAUSS_SEIDEL;
			mainLog.printWarning("Cannot compute exact linear programming. GLPK libraries are not properly installed");
			mainLog.printWarning("Switching to MDP solution method \"" + mdpSolnMethod.fullName() + "\"");
		}

		// Check for some unsupported combinations
		if (mdpSolnMethod == MDPSolnMethod.VALUE_ITERATION && valIterDir == ValIterDir.ABOVE) {
			if (!(precomp && prob0))
				throw new PrismException("Precomputation (Prob0) must be enabled for value iteration from above");
			if (!min)
				throw new PrismException("Value iteration from above only works for minimum probabilities");
		}
		if (mdpSolnMethod == MDPSolnMethod.POLICY_ITERATION || mdpSolnMethod == MDPSolnMethod.MODIFIED_POLICY_ITERATION) {
			if (known != null) {
				throw new PrismException("Policy iteration methods cannot be passed 'known' values for some states");
			}
		}

		// Start probabilistic reachability
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting probabilistic reachability (" + (min ? "min" : "max") + ")...");

		// Check for deadlocks in non-target state (because breaks e.g. prob1)
		mdp.checkForDeadlocks(target);

		// Store num states
		n = mdp.getNumStates();

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
				bsInit.set(i, mdp.isInitialState(i));
			}
			List<BitSet> labels = Arrays.asList(bsInit, target);
			List<String> labelNames = Arrays.asList("init", "target");
			mainLog.println("\nExporting target states info to file \"" + getExportTargetFilename() + "\"...");
			exportLabels(mdp, labels, labelNames, Prism.EXPORT_PLAIN, new PrismFileLog(getExportTargetFilename()));
		}

		// If required, create/initialise strategy storage
		// Set choices to -1, denoting unknown
		// (except for target states, which are -2, denoting arbitrary)
		if (genStrat || exportAdv) {
			strat = new int[n];
			for (int i = 0; i < n; i++) {
				strat[i] = target.get(i) ? -2 : -1;
			}
		}

		// Precomputation
		timerProb0 = System.currentTimeMillis();
		if (precomp && prob0) {
			no = prob0(mdp, remain, target, min, strat);
		} else {
			no = new BitSet();
		}
		timerProb0 = System.currentTimeMillis() - timerProb0;
		timerProb1 = System.currentTimeMillis();
		if (precomp && prob1) {
			yes = prob1(mdp, remain, target, min, strat);
		} else {
			yes = (BitSet) target.clone();
		}
		timerProb1 = System.currentTimeMillis() - timerProb1;

		// Print results of precomputation
		numYes = yes.cardinality();
		numNo = no.cardinality();
		mainLog.println("target=" + target.cardinality() + ", yes=" + numYes + ", no=" + numNo + ", maybe=" + (n - (numYes + numNo)));

		// If still required, store strategy for no/yes (0/1) states.
		// This is just for the cases max=0 and min=1, where arbitrary choices suffice (denoted by -2)
		if (genStrat || exportAdv) {
			if (min) {
				for (int i = yes.nextSetBit(0); i >= 0; i = yes.nextSetBit(i + 1)) {
					if (!target.get(i))
						strat[i] = -2;
				}
			} else {
				for (int i = no.nextSetBit(0); i >= 0; i = no.nextSetBit(i + 1)) {
					strat[i] = -2;
				}
			}
		}

		// Compute probabilities (if needed)
		if (numYes + numNo < n) {
			switch (mdpSolnMethod) {
			case VALUE_ITERATION:
				res = computeReachProbsValIter(mdp, no, yes, min, init, known, strat);
				break;
			case GAUSS_SEIDEL:
				res = computeReachProbsGaussSeidel(mdp, no, yes, min, init, known, strat);
				break;
			case POLICY_ITERATION:
				res = computeReachProbsPolIter(mdp, no, yes, min, strat);
				break;
			case MODIFIED_POLICY_ITERATION:
				res = computeReachProbsModPolIter(mdp, no, yes, min, strat);
				break;
			case EXACT_LINEAR_PROGRAMMING:
				res = computeReachProbsExactLinearProg(mdp, no, yes, target, min, strat);
				break;
			default:
				throw new PrismException("Unknown MDP solution method " + mdpSolnMethod.fullName());
			}
		} else {
			res = new ModelCheckerResult();
			res.soln = Utils.bitsetToDoubleArray(yes, n);
		}

		// Finished probabilistic reachability
		timer = System.currentTimeMillis() - timer;
		mainLog.println("Probabilistic reachability took " + timer / 1000.0 + " seconds.");

		// Store strategy
		if (genStrat) {
			res.strat = new MDStrategyArray(mdp, strat);
		}
		// Export adversary
		if (exportAdv) {
			// Prune strategy
			restrictStrategyToReachableStates(mdp, strat);
			// Export
			PrismLog out = new PrismFileLog(exportAdvFilename);
			new DTMCFromMDPMemorylessAdversary(mdp, strat).exportToPrismExplicitTra(out);
			out.close();
		}

		// Update time taken
		res.timeTaken = timer / 1000.0;
		res.timeProb0 = timerProb0 / 1000.0;
		res.timePre = (timerProb0 + timerProb1) / 1000.0;

		return res;
	}

	/**
	 * Prob0 precomputation algorithm.
	 * i.e. determine the states of an MDP which, with min/max probability 0,
	 * reach a state in {@code target}, while remaining in those in {@code remain}.
	 * {@code min}=true gives Prob0E, {@code min}=false gives Prob0A. 
	 * Optionally, for min only, store optimal (memoryless) strategy info for 0 states. 
	 * @param mdp The MDP
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param min Min or max probabilities (true=min, false=max)
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 */
	public BitSet prob0(MDP mdp, BitSet remain, BitSet target, boolean min, int strat[])
	{
		int n, iters;
		BitSet u, soln, unknown;
		boolean u_done;
		long timer;

		// Start precomputation
		timer = System.currentTimeMillis();
		mainLog.println("Starting Prob0 (" + (min ? "min" : "max") + ")...");

		// Special case: no target states
		if (target.cardinality() == 0) {
			soln = new BitSet(mdp.getNumStates());
			soln.set(0, mdp.getNumStates());
			return soln;
		}

		// Initialise vectors
		n = mdp.getNumStates();
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
			mdp.prob0step(unknown, u, min, soln);
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
		mainLog.print("Prob0 (" + (min ? "min" : "max") + ")");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		// If required, generate strategy. This is for min probs,
		// so it can be done *after* the main prob0 algorithm (unlike for prob1).
		// We simply pick, for all "no" states, the first choice for which all transitions stay in "no"
		if (strat != null) {
			for (int i = u.nextSetBit(0); i >= 0; i = u.nextSetBit(i + 1)) {
				int numChoices = mdp.getNumChoices(i);
				for (int k = 0; k < numChoices; k++) {
					if (mdp.allSuccessorsInSet(i, k, u)) {
						strat[i] = k;
						continue;
					}
				}
			}
		}

		return u;
	}

	/**
	 * Prob1 precomputation algorithm.
	 * i.e. determine the states of an MDP which, with min/max probability 1,
	 * reach a state in {@code target}, while remaining in those in {@code remain}.
	 * {@code min}=true gives Prob1A, {@code min}=false gives Prob1E. 
	 * Optionally, for max only, store optimal (memoryless) strategy info for 1 states. 
	 * @param mdp The MDP
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param min Min or max probabilities (true=min, false=max)
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 */
	public BitSet prob1(MDP mdp, BitSet remain, BitSet target, boolean min, int strat[])
	{
		int n, iters;
		BitSet u, v, soln, unknown;
		boolean u_done, v_done;
		long timer;

		// Start precomputation
		timer = System.currentTimeMillis();
		mainLog.println("Starting Prob1 (" + (min ? "min" : "max") + ")...");

		// Special case: no target states
		if (target.cardinality() == 0) {
			return new BitSet(mdp.getNumStates());
		}

		// Initialise vectors
		n = mdp.getNumStates();
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
				if (min)
					mdp.prob1Astep(unknown, u, v, soln);
				else
					mdp.prob1Estep(unknown, u, v, soln, null);
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

		// If we need to generate a strategy, do another iteration of the inner loop for this
		// We could do this during the main double fixed point above, but we would generate surplus
		// strategy info for non-1 states during early iterations of the outer loop,
		// which are not straightforward to remove since this method does not know which states
		// already have valid strategy info from Prob0.
		// Notice that we only need to look at states in u (since we already know the answer),
		// so we restrict 'unknown' further 
		unknown.and(u);
		if (!min && strat != null) {
			v_done = false;
			v.clear();
			v.or(target);
			soln.clear();
			soln.or(target);
			while (!v_done) {
				mdp.prob1Estep(unknown, u, v, soln, strat);
				v_done = soln.equals(v);
				v.clear();
				v.or(soln);
			}
			u_done = v.equals(u);
		}

		// Finished precomputation
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Prob1 (" + (min ? "min" : "max") + ")");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		return u;
	}

	/**
	 * Compute reachability probabilities using value iteration.
	 * Optionally, store optimal (memoryless) strategy info. 
	 * @param mdp The MDP
	 * @param no Probability 0 states
	 * @param yes Probability 1 states
	 * @param min Min or max probabilities (true=min, false=max)
	 * @param init Optionally, an initial solution vector (will be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values.  
	 */
	protected ModelCheckerResult computeReachProbsValIter(MDP mdp, BitSet no, BitSet yes, boolean min, double init[], BitSet known, int strat[])
			throws PrismException
	{
		ModelCheckerResult res;
		BitSet unknown;
		int i, n, iters;
		double soln[], soln2[], tmpsoln[], initVal;
		boolean done;
		long timer;

		// Start value iteration
		timer = System.currentTimeMillis();
		mainLog.println("Starting value iteration (" + (min ? "min" : "max") + ")...");

		// Store num states
		n = mdp.getNumStates();

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
			// Matrix-vector multiply and min/max ops
			mdp.mvMultMinMax(soln, min, soln2, unknown, false, strat);
			// Check termination
			done = PrismUtils.doublesAreClose(soln, soln2, termCritParam, termCrit == TermCrit.ABSOLUTE);
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished value iteration
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Value iteration (" + (min ? "min" : "max") + ")");
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
	 * Compute reachability probabilities using Gauss-Seidel (including Jacobi-style updates).
	 * @param mdp The MDP
	 * @param no Probability 0 states
	 * @param yes Probability 1 states
	 * @param min Min or max probabilities (true=min, false=max)
	 * @param init Optionally, an initial solution vector (will be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values.  
	 */
	protected ModelCheckerResult computeReachProbsGaussSeidel(MDP mdp, BitSet no, BitSet yes, boolean min, double init[], BitSet known, int strat[])
			throws PrismException
	{
		ModelCheckerResult res;
		BitSet unknown;
		int i, n, iters;
		double soln[], initVal, maxDiff;
		boolean done;
		long timer;

		// Start value iteration
		timer = System.currentTimeMillis();
		mainLog.println("Starting Gauss-Seidel (" + (min ? "min" : "max") + ")...");

		// Store num states
		n = mdp.getNumStates();

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
			maxDiff = mdp.mvMultGSMinMax(soln, min, unknown, false, termCrit == TermCrit.ABSOLUTE, strat);
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
	 * Compute reachability probabilities using policy iteration.
	 * Optionally, store optimal (memoryless) strategy info. 
	 * @param mdp: The MDP
	 * @param no: Probability 0 states
	 * @param yes: Probability 1 states
	 * @param min: Min or max probabilities (true=min, false=max)
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 */
	protected ModelCheckerResult computeReachProbsPolIter(MDP mdp, BitSet no, BitSet yes, boolean min, int strat[]) throws PrismException
	{
		ModelCheckerResult res;
		int i, n, iters, totalIters;
		double soln[], soln2[];
		boolean done;
		long timer;
		DTMCModelChecker mcDTMC;
		DTMC dtmc;

		// Re-use solution to solve each new policy (strategy)?
		boolean reUseSoln = true;

		// Start policy iteration
		timer = System.currentTimeMillis();
		mainLog.println("Starting policy iteration (" + (min ? "min" : "max") + ")...");

		// Create a DTMC model checker (for solving policies)
		mcDTMC = new DTMCModelChecker(this);
		mcDTMC.inheritSettings(this);
		mcDTMC.setLog(new PrismDevNullLog());

		// Store num states
		n = mdp.getNumStates();

		// Create solution vectors
		soln = new double[n];
		soln2 = new double[n];

		// Initialise solution vectors.
		for (i = 0; i < n; i++)
			soln[i] = soln2[i] = yes.get(i) ? 1.0 : 0.0;

		// If not passed in, create new storage for strategy and initialise
		// Initial strategy just picks first choice (0) everywhere
		if (strat == null) {
			strat = new int[n];
			for (i = 0; i < n; i++)
				strat[i] = 0;
		}
		// Otherwise, just initialise for states not in yes/no
		// (Optimal choices for yes/no should already be known)
		else {
			for (i = 0; i < n; i++)
				if (!(no.get(i) || yes.get(i)))
					strat[i] = 0;
		}

		// Start iterations
		iters = totalIters = 0;
		done = false;
		while (!done) {
			iters++;
			// Solve induced DTMC for strategy
			dtmc = new DTMCFromMDPMemorylessAdversary(mdp, strat);
			res = mcDTMC.computeReachProbsGaussSeidel(dtmc, no, yes, reUseSoln ? soln : null, null);
			soln = res.soln;
			totalIters += res.numIters;
			// Check if optimal, improve non-optimal choices
			mdp.mvMultMinMax(soln, min, soln2, null, false, null);
			done = true;
			for (i = 0; i < n; i++) {
				// Don't look at no/yes states - we may not have strategy info for them,
				// so they might appear non-optimal
				if (no.get(i) || yes.get(i))
					continue;
				if (!PrismUtils.doublesAreClose(soln[i], soln2[i], termCritParam, termCrit == TermCrit.ABSOLUTE)) {
					done = false;
					List<Integer> opt = mdp.mvMultMinMaxSingleChoices(i, soln, min, soln2[i]);
					// Only update strategy if strictly better
					if (!opt.contains(strat[i]))
						strat[i] = opt.get(0);
				}
			}
		}

		// Finished policy iteration
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Policy iteration");
		mainLog.println(" took " + iters + " cycles (" + totalIters + " iterations in total) and " + timer / 1000.0 + " seconds.");

		// Return results
		// (Note we don't add the strategy - the one passed in is already there
		// and might have some existing choices stored for other states).
		res = new ModelCheckerResult();
		res.soln = soln;
		res.numIters = totalIters;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Compute reachability probabilities using modified policy iteration.
	 * @param mdp: The MDP
	 * @param no: Probability 0 states
	 * @param yes: Probability 1 states
	 * @param min: Min or max probabilities (true=min, false=max)
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 */
	protected ModelCheckerResult computeReachProbsModPolIter(MDP mdp, BitSet no, BitSet yes, boolean min, int strat[]) throws PrismException
	{
		ModelCheckerResult res;
		int i, n, iters, totalIters;
		double soln[], soln2[];
		boolean done;
		long timer;
		DTMCModelChecker mcDTMC;
		DTMC dtmc;

		// Start value iteration
		timer = System.currentTimeMillis();
		mainLog.println("Starting modified policy iteration (" + (min ? "min" : "max") + ")...");

		// Create a DTMC model checker (for solving policies)
		mcDTMC = new DTMCModelChecker(this);
		mcDTMC.inheritSettings(this);
		mcDTMC.setLog(new PrismDevNullLog());

		// Limit iters for DTMC solution - this implements "modified" policy iteration
		mcDTMC.setMaxIters(100);
		mcDTMC.setErrorOnNonConverge(false);

		// Store num states
		n = mdp.getNumStates();

		// Create solution vectors
		soln = new double[n];
		soln2 = new double[n];

		// Initialise solution vectors.
		for (i = 0; i < n; i++)
			soln[i] = soln2[i] = yes.get(i) ? 1.0 : 0.0;

		// If not passed in, create new storage for strategy and initialise
		// Initial strategy just picks first choice (0) everywhere
		if (strat == null) {
			strat = new int[n];
			for (i = 0; i < n; i++)
				strat[i] = 0;
		}
		// Otherwise, just initialise for states not in yes/no
		// (Optimal choices for yes/no should already be known)
		else {
			for (i = 0; i < n; i++)
				if (!(no.get(i) || yes.get(i)))
					strat[i] = 0;
		}

		// Start iterations
		iters = totalIters = 0;
		done = false;
		while (!done) {
			iters++;
			// Solve induced DTMC for strategy
			dtmc = new DTMCFromMDPMemorylessAdversary(mdp, strat);
			res = mcDTMC.computeReachProbsGaussSeidel(dtmc, no, yes, soln, null);
			soln = res.soln;
			totalIters += res.numIters;
			// Check if optimal, improve non-optimal choices
			mdp.mvMultMinMax(soln, min, soln2, null, false, null);
			done = true;
			for (i = 0; i < n; i++) {
				// Don't look at no/yes states - we don't store strategy info for them,
				// so they might appear non-optimal
				if (no.get(i) || yes.get(i))
					continue;
				if (!PrismUtils.doublesAreClose(soln[i], soln2[i], termCritParam, termCrit == TermCrit.ABSOLUTE)) {
					done = false;
					List<Integer> opt = mdp.mvMultMinMaxSingleChoices(i, soln, min, soln2[i]);
					strat[i] = opt.get(0);
				}
			}
		}

		// Finished policy iteration
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Modified policy iteration");
		mainLog.println(" took " + iters + " cycles (" + totalIters + " iterations in total) and " + timer / 1000.0 + " seconds.");

		// Return results
		// (Note we don't add the strategy - the one passed in is already there
		// and might have some existing choices stored for other states).
		res = new ModelCheckerResult();
		res.soln = soln;
		res.numIters = totalIters;
		res.timeTaken = timer / 1000.0;
		return res;
	}
	
	/**
	 * Compute arbitrary precision reachability probabilities using linear programming.
	 * @param mdp: The MDP
	 * @param no: Probability 0 states
	 * @param yes: Probability 1 states
	 * @param target: Target states
	 * @param min: Min or max probabilities (true=min, false=max)
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 */
	protected ModelCheckerResult computeReachProbsExactLinearProg(MDP mdp, BitSet no, BitSet yes, BitSet target, boolean min, int strat[]) throws PrismException
	{
		ModelCheckerResult res;
		int nStates, maybeSize, countMaybeTrans, ret;
		double sol, soln[], matAEntry, bEntry;
		long timer, basisTimer, matATimer, exactSolverTimer;
		BitSet maybe;
		SWIGTYPE_p_int ind;
		SWIGTYPE_p_double val;
		glp_smcp parm;
		glp_prob lp;

		// Start linear programming
		timer = System.currentTimeMillis();
		mainLog.println("Starting exact linear programming (" + (min ? "min" : "max") + ")...");

		// Store num states
		nStates = mdp.getNumStates();

		// Solution vector where we store the exact
		// probabilities as doubles
		soln = new double[nStates];
		BitSet states = new BitSet();
		states.set(0, nStates);

		// Determine the set of maybe states (S?)
		maybe = new BitSet();
		maybe.set(0, nStates);
		maybe.andNot(yes);
		maybe.andNot(no);

		// Store the cardinality of the maybe state
		maybeSize = maybe.cardinality();

		// The set of basic columns.
		// This set will be filled as defined in (10)
		Set<Integer> basicCols = new HashSet<Integer>();

		// A mapping between maybe states and its positions in the maybe bitset.
		// This is useful for calculating the `A` matrix later on.
		// Also, it is calculated the number of the transitions of all maybe states `countMaybeTrans`
		countMaybeTrans = 0;
		HashMap<Integer,Integer> maybeToState = new HashMap<Integer,Integer>();
		HashMap<Integer,Integer> stateToMaybe = new HashMap<Integer,Integer>();
		int maybeStateCount = 1;
		for(int state = maybe.nextSetBit(0); state >= 0; state = maybe.nextSetBit(state + 1)) {
			maybeToState.put(maybeStateCount, state);
			stateToMaybe.put(state, maybeStateCount);
			countMaybeTrans += mdp.getNumChoices(state);
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
			GLPK.glp_set_row_name(lp, row, "s" + maybe.nextSetBit(row));
			if (min) {
				GLPK.glp_set_row_bnds(lp, row, GLPKConstants.GLP_UP, 0, -1);
				GLPK.glp_set_obj_dir(lp, GLPKConstants.GLP_MAX);
			} else {
				GLPK.glp_set_row_bnds(lp, row, GLPKConstants.GLP_LO, -1, 0);
				GLPK.glp_set_obj_dir(lp, GLPKConstants.GLP_MIN);
			}
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
		for (int state = maybe.nextSetBit(0); state >= 0; state = maybe.nextSetBit(state + 1)) {
			for (int choice = 0; choice < mdp.getNumChoices(state); choice++) {
				// Index of the i-th equation in the lp's matrix
				int eqIndex = 1;
				Iterator<Map.Entry<Integer, Double>> iter = mdp.getTransitionsIterator(state, choice);
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
					if (maybe.get(actualKey)) {
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
				// This is described in (10) on the paper
				// If strat is null, it would mean that the strategy is not apt, so we should ignore
				// the basis construction for this case
				if (strat != null && choice == strat[state])
					basicCols.add(currentTransition);

				// Set the values of the arrays in the full linear programming equation matrix.
				// Negate the summation calculated for the constraint vector entries
				GLPK.glp_set_col_bnds(lp, currentTransition, GLPKConstants.GLP_LO, 0, 0);
				GLPK.glp_set_mat_col(lp, currentTransition, eqIndex - 1, ind, val);
				GLPK.glp_set_obj_coef(lp, currentTransition, -bEntry);

				currentTransition++;
			}
		}
		mainLog.println("Linear programming equations construction time: " +
				((double)System.currentTimeMillis() - matATimer)/1000 + " seconds");

		// Determine the valid initial basis defined in (10).
		// Set every basic column as basic (GLP_BS constant), otherwise
		// it is non-basic having an active lower bound (GLP_NL)
		basisTimer = System.currentTimeMillis();
		for (int col = 1; col < currentTransition; col++) {
			if (basicCols.contains(col)) {
				GLPK.glp_set_col_stat(lp, col, GLPKConstants.GLP_BS);
			} else {
				GLPK.glp_set_col_stat(lp, col, GLPKConstants.GLP_NL);
			}
		}
		mainLog.println("Basis construction time: " +
				((double)System.currentTimeMillis() - basisTimer)/1000 + " seconds");

		// Solving the linear problem in the linear programming library GLPK.
		// probs[]: an array for storing the exact probabilities as string in the form `p/q`
		// `num` and `den` store the temporal `p` and `q` respectively (this could be avoided)
		String probs[] = new String[nStates];

		// Set up fixed parameters
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

		mainLog.println("\n" + this.getPrecision() + "-bit results (non-zero only) for each state of the MDP:");
		for (int mdpState = 0; mdpState < nStates; mdpState++) {
			if (maybe.get(mdpState)) {
				sol = GLPK.glp_get_row_dual(lp, stateToMaybe.get(mdpState));
				soln[mdpState] = sol;
				currentResult = GLPK.uint8Array_toString(GLPK.uint8ArrayArray_getitem(GLPK.glp_get_probs(lp), stateToMaybe.get(mdpState) - 1));
				exp = GLPK.intArray_getitem(GLPK.glp_get_exps(lp), stateToMaybe.get(mdpState) - 1);
				// We need to format the output since we get the exponent as a position in the string
				String zeroes = "";
				for (int nZero = 0; nZero < Math.abs(exp); nZero++)
					zeroes += "0";
				currentResult = exp > 0 ? new StringBuilder(currentResult).insert(exp, ".").toString() : "0." + zeroes + currentResult;
				probs[mdpState] = currentResult;
			}
			// If it is a `yes` state, its probability is 1
			else if (yes.get(mdpState)) {
				soln[mdpState] = 1.;
				probs[mdpState] = "1";
			}
			// If it is a `no` state, its probability is 0
			else if (no.get(mdpState)) {
				soln[mdpState] = 0.;
				probs[mdpState] = "0";
			}
			// Avoid zero entries
			if (probs[mdpState] != "0")
				mainLog.println("[" + mdpState + "]: " + probs[mdpState]);
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

		// Finished linear programming
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Exact linear programming");
		mainLog.println(" took " + timer / 1000.0 + " seconds.");

		// Return results
		// (Note we don't add the strategy - the one passed in is already there
		// and might have some existing choices stored for other states).
		res = new ModelCheckerResult();
		res.timeTaken = timer / 1000.0;
		res.soln = soln;
		return res;
	}

	/**
	 * Construct strategy information for min/max reachability probabilities.
	 * (More precisely, list of indices of choices resulting in min/max.)
	 * (Note: indices are guaranteed to be sorted in ascending order.)
	 * @param mdp The MDP
	 * @param state The state to generate strategy info for
	 * @param target The set of target states to reach
	 * @param min Min or max probabilities (true=min, false=max)
	 * @param lastSoln Vector of values from which to recompute in one iteration 
	 */
	public List<Integer> probReachStrategy(MDP mdp, int state, BitSet target, boolean min, double lastSoln[]) throws PrismException
	{
		double val = mdp.mvMultMinMaxSingle(state, lastSoln, min, null);
		return mdp.mvMultMinMaxSingleChoices(state, lastSoln, min, val);
	}

	/**
	 * Compute bounded reachability probabilities.
	 * i.e. compute the min/max probability of reaching a state in {@code target} within k steps.
	 * @param mdp The MDP
	 * @param target Target states
	 * @param k Bound
	 * @param min Min or max probabilities (true=min, false=max)
	 */
	public ModelCheckerResult computeBoundedReachProbs(MDP mdp, BitSet target, int k, boolean min) throws PrismException
	{
		return computeBoundedReachProbs(mdp, null, target, k, min, null, null);
	}

	/**
	 * Compute bounded until probabilities.
	 * i.e. compute the min/max probability of reaching a state in {@code target},
	 * within k steps, and while remaining in states in {@code remain}.
	 * @param mdp The MDP
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param k Bound
	 * @param min Min or max probabilities (true=min, false=max)
	 */
	public ModelCheckerResult computeBoundedUntilProbs(MDP mdp, BitSet remain, BitSet target, int k, boolean min) throws PrismException
	{
		return computeBoundedReachProbs(mdp, remain, target, k, min, null, null);
	}

	/**
	 * Compute bounded reachability/until probabilities.
	 * i.e. compute the min/max probability of reaching a state in {@code target},
	 * within k steps, and while remaining in states in {@code remain}.
	 * @param mdp The MDP
	 * @param remain Remain in these states (optional: null means "all")
	 * @param target Target states
	 * @param k Bound
	 * @param min Min or max probabilities (true=min, false=max)
	 * @param init Optionally, an initial solution vector (may be overwritten) 
	 * @param results Optional array of size k+1 to store (init state) results for each step (null if unused)
	 */
	public ModelCheckerResult computeBoundedReachProbs(MDP mdp, BitSet remain, BitSet target, int k, boolean min, double init[], double results[])
			throws PrismException
	{
		ModelCheckerResult res = null;
		BitSet unknown;
		int i, n, iters;
		double soln[], soln2[], tmpsoln[];
		long timer;

		// Start bounded probabilistic reachability
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting bounded probabilistic reachability (" + (min ? "min" : "max") + ")...");

		// Store num states
		n = mdp.getNumStates();

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
			results[0] = Utils.minMaxOverArraySubset(soln2, mdp.getInitialStates(), true);
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
			// Matrix-vector multiply and min/max ops
			mdp.mvMultMinMax(soln, min, soln2, unknown, false, null);
			// Store intermediate results if required
			// (compute min/max value over initial states for this step)
			if (results != null) {
				// TODO: whether this is min or max should be specified somehow
				results[iters] = Utils.minMaxOverArraySubset(soln2, mdp.getInitialStates(), true);
			}
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished bounded probabilistic reachability
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Bounded probabilistic reachability (" + (min ? "min" : "max") + ")");
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
	 * Compute expected cumulative (step-bounded) rewards.
	 * i.e. compute the min/max reward accumulated within {@code k} steps.
	 * @param mdp The MDP
	 * @param mdpRewards The rewards
	 * @param target Target states
	 * @param min Min or max rewards (true=min, false=max)
	 */
	public ModelCheckerResult computeCumulativeRewards(MDP mdp, MDPRewards mdpRewards, int k, boolean min) throws PrismException
	{
		ModelCheckerResult res = null;
		int i, n, iters;
		long timer;
		double soln[], soln2[], tmpsoln[];

		// Start expected cumulative reward
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting expected cumulative reward (" + (min ? "min" : "max") + ")...");

		// Store num states
		n = mdp.getNumStates();

		// Create/initialise solution vector(s)
		soln = new double[n];
		soln2 = new double[n];
		for (i = 0; i < n; i++)
			soln[i] = soln2[i] = 0.0;

		// Start iterations
		iters = 0;
		while (iters < k) {
			iters++;
			// Matrix-vector multiply and min/max ops
			mdp.mvMultRewMinMax(soln, mdpRewards, min, soln2, null, false, null);
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished value iteration
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Expected cumulative reward (" + (min ? "min" : "max") + ")");
		mainLog.println(" took " + iters + " iterations and " + timer / 1000.0 + " seconds.");

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.numIters = iters;
		res.timeTaken = timer / 1000.0;

		return res;
	}

	/**
	 * Compute expected instantaneous reward,
	 * i.e. compute the min/max expected reward of the states after {@code k} steps.
	 * @param mdp The MDP
	 * @param mdpRewards The rewards
	 * @param k the number of steps
	 * @param min Min or max rewards (true=min, false=max)
	 */
	public ModelCheckerResult computeInstantaneousRewards(MDP mdp, MDPRewards mdpRewards, final int k, boolean min)
	{
		ModelCheckerResult res = null;
		int i, n, iters;
		double soln[], soln2[], tmpsoln[];
		long timer;

		// Store num states
		n = mdp.getNumStates();

		// Start backwards transient computation
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting backwards instantaneous rewards computation...");

		// Create solution vector(s)
		soln = new double[n];
		soln2 = new double[n];

		// Initialise solution vectors.
		for (i = 0; i < n; i++)
			soln[i] = mdpRewards.getStateReward(i);

		// Start iterations
		for (iters = 0; iters < k; iters++) {
			// Matrix-vector multiply
			mdp.mvMultMinMax(soln, min, soln2, null, false, null);
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

	/**
	 * Compute expected reachability rewards.
	 * @param mdp The MDP
	 * @param mdpRewards The rewards
	 * @param target Target states
	 * @param min Min or max rewards (true=min, false=max)
	 */
	public ModelCheckerResult computeReachRewards(MDP mdp, MDPRewards mdpRewards, BitSet target, boolean min) throws PrismException
	{
		return computeReachRewards(mdp, mdpRewards, target, min, null, null);
	}

	/**
	 * Compute expected reachability rewards.
	 * i.e. compute the min/max reward accumulated to reach a state in {@code target}.
	 * @param mdp The MDP
	 * @param mdpRewards The rewards
	 * @param target Target states
	 * @param min Min or max rewards (true=min, false=max)
	 * @param init Optionally, an initial solution vector (may be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values).  
	 * Also, 'known' values cannot be passed for some solution methods, e.g. policy iteration.  
	 */
	public ModelCheckerResult computeReachRewards(MDP mdp, MDPRewards mdpRewards, BitSet target, boolean min, double init[], BitSet known)
			throws PrismException
	{
		ModelCheckerResult res = null;
		BitSet inf;
		int n, numTarget, numInf;
		long timer, timerProb1;
		int strat[] = null;
		// Local copy of setting
		MDPSolnMethod mdpSolnMethod = this.mdpSolnMethod;

		// Switch to a supported method, if necessary
		if (!(mdpSolnMethod == MDPSolnMethod.VALUE_ITERATION || mdpSolnMethod == MDPSolnMethod.GAUSS_SEIDEL || mdpSolnMethod == MDPSolnMethod.POLICY_ITERATION)) {
			mdpSolnMethod = MDPSolnMethod.GAUSS_SEIDEL;
			mainLog.printWarning("Switching to MDP solution method \"" + mdpSolnMethod.fullName() + "\"");
		}

		// Check for some unsupported combinations
		if (mdpSolnMethod == MDPSolnMethod.POLICY_ITERATION) {
			if (known != null) {
				throw new PrismException("Policy iteration methods cannot be passed 'known' values for some states");
			}
		}
		
		// Start expected reachability
		timer = System.currentTimeMillis();
		mainLog.println("\nStarting expected reachability (" + (min ? "min" : "max") + ")...");

		// Check for deadlocks in non-target state (because breaks e.g. prob1)
		mdp.checkForDeadlocks(target);

		// Store num states
		n = mdp.getNumStates();
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
				bsInit.set(i, mdp.isInitialState(i));
			}
			List<BitSet> labels = Arrays.asList(bsInit, target);
			List<String> labelNames = Arrays.asList("init", "target");
			mainLog.println("\nExporting target states info to file \"" + getExportTargetFilename() + "\"...");
			exportLabels(mdp, labels, labelNames, Prism.EXPORT_PLAIN, new PrismFileLog(getExportTargetFilename()));
		}

		// If required, create/initialise strategy storage
		// Set choices to -1, denoting unknown
		// (except for target states, which are -2, denoting arbitrary)
		if (genStrat || exportAdv || mdpSolnMethod == MDPSolnMethod.POLICY_ITERATION) {
			strat = new int[n];
			for (int i = 0; i < n; i++) {
				strat[i] = target.get(i) ? -2 : -1;
			}
		}
		
		// Precomputation (not optional)
		timerProb1 = System.currentTimeMillis();
		inf = prob1(mdp, null, target, !min, strat);
		inf.flip(0, n);
		timerProb1 = System.currentTimeMillis() - timerProb1;
		
		// Print results of precomputation
		numTarget = target.cardinality();
		numInf = inf.cardinality();
		mainLog.println("target=" + numTarget + ", inf=" + numInf + ", rest=" + (n - (numTarget + numInf)));

		// If required, generate strategy for "inf" states.
		if (genStrat || exportAdv || mdpSolnMethod == MDPSolnMethod.POLICY_ITERATION) {
			if (min) {
				// If min reward is infinite, all choices give infinity
				// So the choice can be arbitrary, denoted by -2; 
				for (int i = inf.nextSetBit(0); i >= 0; i = inf.nextSetBit(i + 1)) {
					strat[i] = -2;
				}
			} else {
				// If max reward is infinite, there is at least one choice giving infinity.
				// So we pick, for all "inf" states, the first choice for which some transitions stays in "inf".
				for (int i = inf.nextSetBit(0); i >= 0; i = inf.nextSetBit(i + 1)) {
					int numChoices = mdp.getNumChoices(i);
					for (int k = 0; k < numChoices; k++) {
						if (mdp.someSuccessorsInSet(i, k, inf)) {
							strat[i] = k;
							continue;
						}
					}
				}
			}
		}

		// Compute rewards
		switch (mdpSolnMethod) {
		case VALUE_ITERATION:
			res = computeReachRewardsValIter(mdp, mdpRewards, target, inf, min, init, known, strat);
			break;
		case GAUSS_SEIDEL:
			res = computeReachRewardsGaussSeidel(mdp, mdpRewards, target, inf, min, init, known, strat);
			break;
		case POLICY_ITERATION:
			res = computeReachRewardsPolIter(mdp, mdpRewards, target, inf, min, strat);
			break;
		default:
			throw new PrismException("Unknown MDP solution method " + mdpSolnMethod.fullName());
		}

		// Store strategy
		if (genStrat) {
			res.strat = new MDStrategyArray(mdp, strat);
		}
		// Export adversary
		if (exportAdv) {
			// Prune strategy
			restrictStrategyToReachableStates(mdp, strat);
			// Export
			PrismLog out = new PrismFileLog(exportAdvFilename);
			new DTMCFromMDPMemorylessAdversary(mdp, strat).exportToPrismExplicitTra(out);
			out.close();
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
	 * Optionally, store optimal (memoryless) strategy info. 
	 * @param mdp The MDP
	 * @param mdpRewards The rewards
	 * @param target Target states
	 * @param inf States for which reward is infinite
	 * @param min Min or max rewards (true=min, false=max)
	 * @param init Optionally, an initial solution vector (will be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values.
	 */
	protected ModelCheckerResult computeReachRewardsValIter(MDP mdp, MDPRewards mdpRewards, BitSet target, BitSet inf, boolean min, double init[], BitSet known, int strat[])
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
		mainLog.println("Starting value iteration (" + (min ? "min" : "max") + ")...");

		// Store num states
		n = mdp.getNumStates();

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
			// Matrix-vector multiply and min/max ops
			mdp.mvMultRewMinMax(soln, mdpRewards, min, soln2, unknown, false, strat);
			// Check termination
			done = PrismUtils.doublesAreClose(soln, soln2, termCritParam, termCrit == TermCrit.ABSOLUTE);
			// Swap vectors for next iter
			tmpsoln = soln;
			soln = soln2;
			soln2 = tmpsoln;
		}

		// Finished value iteration
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Value iteration (" + (min ? "min" : "max") + ")");
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
	 * Compute expected reachability rewards using Gauss-Seidel (including Jacobi-style updates).
	 * Optionally, store optimal (memoryless) strategy info. 
	 * @param mdp The MDP
	 * @param mdpRewards The rewards
	 * @param target Target states
	 * @param inf States for which reward is infinite
	 * @param min Min or max rewards (true=min, false=max)
	 * @param init Optionally, an initial solution vector (will be overwritten) 
	 * @param known Optionally, a set of states for which the exact answer is known
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 * Note: if 'known' is specified (i.e. is non-null, 'init' must also be given and is used for the exact values.
	 */
	protected ModelCheckerResult computeReachRewardsGaussSeidel(MDP mdp, MDPRewards mdpRewards, BitSet target, BitSet inf, boolean min, double init[],
			BitSet known, int strat[]) throws PrismException
	{
		ModelCheckerResult res;
		BitSet unknown;
		int i, n, iters;
		double soln[], maxDiff;
		boolean done;
		long timer;

		// Start value iteration
		timer = System.currentTimeMillis();
		mainLog.println("Starting Gauss-Seidel (" + (min ? "min" : "max") + ")...");

		// Store num states
		n = mdp.getNumStates();

		// Create solution vector(s)
		soln = (init == null) ? new double[n] : init;

		// Initialise solution vector. Use (where available) the following in order of preference:
		// (1) exact answer, if already known; (2) 0.0/infinity if in target/inf; (3) passed in initial value; (4) 0.0
		if (init != null) {
			if (known != null) {
				for (i = 0; i < n; i++)
					soln[i] = known.get(i) ? init[i] : target.get(i) ? 0.0 : inf.get(i) ? Double.POSITIVE_INFINITY : init[i];
			} else {
				for (i = 0; i < n; i++)
					soln[i] = target.get(i) ? 0.0 : inf.get(i) ? Double.POSITIVE_INFINITY : init[i];
			}
		} else {
			for (i = 0; i < n; i++)
				soln[i] = target.get(i) ? 0.0 : inf.get(i) ? Double.POSITIVE_INFINITY : 0.0;
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
			// Matrix-vector multiply and min/max ops
			maxDiff = mdp.mvMultRewGSMinMax(soln, mdpRewards, min, unknown, false, termCrit == TermCrit.ABSOLUTE, strat);
			// Check termination
			done = maxDiff < termCritParam;
		}

		// Finished Gauss-Seidel
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Gauss-Seidel (" + (min ? "min" : "max") + ")");
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
	 * Compute expected reachability rewards using policy iteration.
	 * The array {@code strat} is used both to pass in the initial strategy for policy iteration,
	 * and as storage for the resulting optimal strategy (if needed).
	 * Passing in an initial strategy is required when some states have infinite reward,
	 * to avoid the possibility of policy iteration getting stuck on an infinite-value strategy.
	 * @param mdp The MDP
	 * @param mdpRewards The rewards
	 * @param target Target states
	 * @param inf States for which reward is infinite
	 * @param min Min or max rewards (true=min, false=max)
	 * @param strat Storage for (memoryless) strategy choice indices (ignored if null)
	 */
	protected ModelCheckerResult computeReachRewardsPolIter(MDP mdp, MDPRewards mdpRewards, BitSet target, BitSet inf, boolean min, int strat[])
			throws PrismException
	{
		ModelCheckerResult res;
		int i, n, iters, totalIters;
		double soln[], soln2[];
		boolean done;
		long timer;
		DTMCModelChecker mcDTMC;
		DTMC dtmc;
		MCRewards mcRewards;

		// Re-use solution to solve each new policy (strategy)?
		boolean reUseSoln = true;

		// Start policy iteration
		timer = System.currentTimeMillis();
		mainLog.println("Starting policy iteration (" + (min ? "min" : "max") + ")...");

		// Create a DTMC model checker (for solving policies)
		mcDTMC = new DTMCModelChecker(this);
		mcDTMC.inheritSettings(this);
		mcDTMC.setLog(new PrismDevNullLog());

		// Store num states
		n = mdp.getNumStates();

		// Create solution vector(s)
		soln = new double[n];
		soln2 = new double[n];

		// Initialise solution vectors.
		for (i = 0; i < n; i++)
			soln[i] = soln2[i] = target.get(i) ? 0.0 : inf.get(i) ? Double.POSITIVE_INFINITY : 0.0;

		// If not passed in, create new storage for strategy and initialise
		// Initial strategy just picks first choice (0) everywhere
		if (strat == null) {
			strat = new int[n];
			for (i = 0; i < n; i++)
				strat[i] = 0;
		}
			
		// Start iterations
		iters = totalIters = 0;
		done = false;
		while (!done && iters < maxIters) {
			iters++;
			// Solve induced DTMC for strategy
			dtmc = new DTMCFromMDPMemorylessAdversary(mdp, strat);
			mcRewards = new MCRewardsFromMDPRewards(mdpRewards, strat);
			res = mcDTMC.computeReachRewardsValIter(dtmc, mcRewards, target, inf, reUseSoln ? soln : null, null);
			soln = res.soln;
			totalIters += res.numIters;
			// Check if optimal, improve non-optimal choices
			mdp.mvMultRewMinMax(soln, mdpRewards, min, soln2, null, false, null);
			done = true;
			for (i = 0; i < n; i++) {
				// Don't look at target/inf states - we may not have strategy info for them,
				// so they might appear non-optimal
				if (target.get(i) || inf.get(i))
					continue;
				if (!PrismUtils.doublesAreClose(soln[i], soln2[i], termCritParam, termCrit == TermCrit.ABSOLUTE)) {
					done = false;
					List<Integer> opt = mdp.mvMultRewMinMaxSingleChoices(i, soln, mdpRewards, min, soln2[i]);
					// Only update strategy if strictly better
					if (!opt.contains(strat[i]))
						strat[i] = opt.get(0);
				}
			}
		}

		// Finished policy iteration
		timer = System.currentTimeMillis() - timer;
		mainLog.print("Policy iteration");
		mainLog.println(" took " + iters + " cycles (" + totalIters + " iterations in total) and " + timer / 1000.0 + " seconds.");

		// Return results
		res = new ModelCheckerResult();
		res.soln = soln;
		res.numIters = totalIters;
		res.timeTaken = timer / 1000.0;
		return res;
	}

	/**
	 * Construct strategy information for min/max expected reachability.
	 * (More precisely, list of indices of choices resulting in min/max.)
	 * (Note: indices are guaranteed to be sorted in ascending order.)
	 * @param mdp The MDP
	 * @param mdpRewards The rewards
	 * @param state The state to generate strategy info for
	 * @param target The set of target states to reach
	 * @param min Min or max rewards (true=min, false=max)
	 * @param lastSoln Vector of values from which to recompute in one iteration 
	 */
	public List<Integer> expReachStrategy(MDP mdp, MDPRewards mdpRewards, int state, BitSet target, boolean min, double lastSoln[]) throws PrismException
	{
		double val = mdp.mvMultRewMinMaxSingle(state, lastSoln, mdpRewards, min, null);
		return mdp.mvMultRewMinMaxSingleChoices(state, lastSoln, mdpRewards, min, val);
	}

	/**
	 * Restrict a (memoryless) strategy for an MDP, stored as an integer array of choice indices,
	 * to the states of the MDP that are reachable under that strategy.  
	 * @param mdp The MDP
	 * @param strat The strategy
	 */
	public void restrictStrategyToReachableStates(MDP mdp, int strat[])
	{
		BitSet restrict = new BitSet();
		BitSet explore = new BitSet();
		// Get initial states
		for (int is : mdp.getInitialStates()) {
			restrict.set(is);
			explore.set(is);
		}
		// Compute reachable states (store in 'restrict') 
		boolean foundMore = true;
		while (foundMore) {
			foundMore = false;
			for (int s = explore.nextSetBit(0); s >= 0; s = explore.nextSetBit(s + 1)) {
				explore.set(s, false);
				if (strat[s] >= 0) {
					Iterator<Map.Entry<Integer, Double>> iter = mdp.getTransitionsIterator(s, strat[s]);
					while (iter.hasNext()) {
						Map.Entry<Integer, Double> e = iter.next();
						int dest = e.getKey();
						if (!restrict.get(dest)) {
							foundMore = true;
							restrict.set(dest);
							explore.set(dest);
						}
					}
				}
			}
		}
		// Set strategy choice for non-reachable state to -1
		int n = mdp.getNumStates();
		for (int s = restrict.nextClearBit(0); s < n; s = restrict.nextClearBit(s + 1)) {
			strat[s] = -3;
		}
	}

	/**
	 * Simple test program.
	 */
	public static void main(String args[])
	{
		MDPModelChecker mc;
		MDPSimple mdp;
		ModelCheckerResult res;
		BitSet init, target;
		Map<String, BitSet> labels;
		boolean min = true;
		try {
			mc = new MDPModelChecker(null);
			mdp = new MDPSimple();
			mdp.buildFromPrismExplicit(args[0]);
			mdp.addInitialState(0);
			//System.out.println(mdp);
			labels = StateModelChecker.loadLabelsFile(args[1]);
			//System.out.println(labels);
			init = labels.get("init");
			target = labels.get(args[2]);
			if (target == null)
				throw new PrismException("Unknown label \"" + args[2] + "\"");
			for (int i = 3; i < args.length; i++) {
				if (args[i].equals("-min"))
					min = true;
				else if (args[i].equals("-max"))
					min = false;
				else if (args[i].equals("-nopre"))
					mc.setPrecomp(false);
			}
			res = mc.computeReachProbs(mdp, target, min);
			System.out.println(res.soln[init.nextSetBit(0)]);
		} catch (PrismException e) {
			System.out.println(e);
		}
	}

}
