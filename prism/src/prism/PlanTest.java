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

import java.io.File;
import java.io.FileNotFoundException;
import java.util.Arrays;
import java.util.List;

import explicit.ConstructModel;
import explicit.MDP;
import explicit.MDPModelChecker;
import parser.State;
import parser.VarList;
import parser.ast.Declaration;
import parser.ast.DeclarationInt;
import parser.ast.Expression;
import parser.ast.ModulesFile;
import parser.ast.PropertiesFile;
import parser.type.Type;
import parser.type.TypeInt;

/**
 * Example class demonstrating how to control PRISM programmatically,
 * i.e. through the "API" exposed by the class prism.Prism.
 * (this now uses the newer version of the API, released after PRISM 4.0.3)
 * Test like this:
 * PRISM_MAINCLASS=prism.PlanTest bin/prism
 */
public class PlanTest
{
	public static void main(String args[])
	{
		new PlanTest().go(args);
	}

	public void go(String args[])
	{
		try {
			PrismLog mainLog;
			Prism prism;

			// Init PRISM
			mainLog = new PrismFileLog("stdout");
			prism = new Prism(mainLog);
			prism.initialise();

			// Build model (outside of PRISM)
			int size = 3;
			MDPGenerator mdpGen = new MDPGenerator(size);
			
			/*ConstructModel constructModel = new ConstructModel(prism);
			MDP mdp = (MDP) constructModel.constructModel(mdpGen);
			mdp.exportToDotFile(new PrismFileLog("mdp.dot"), null, true);*/

			// Build the same model through the PRISM API
			prism.loadModelGenerator(mdpGen);
			prism.exportStatesToFile(Prism.EXPORT_PLAIN, new File("adv.sta"));
			prism.exportLabelsToFile(null, Prism.EXPORT_PLAIN, new File("adv.lab"));
			prism.exportTransToFile(true, Prism.EXPORT_DOT_STATES, new File("mdp.dot"));
			//prism.exportStateRewardsToFile(Prism.EXPORT_PLAIN, new File("adv.srew"));
			prism.setExportAdv(Prism.EXPORT_ADV_MDP);
			prism.setExportAdvFilename("adv.tra");
			//propertiesFile = prism.parsePropertiesString(mdpGen, "Pmax=?[F \"target\"]");
			//result = prism.modelCheck(propertiesFile, propertiesFile.getPropertyObject(0));
			//System.out.println(prism.modelCheck("Pmax=?[F \"target\"]").getResult());
			System.out.println(prism.modelCheck("Rmin=?[F \"target\"]").getResult());
			
			/*MDPModelChecker mc = new MDPModelChecker(prism);
			propertiesFile = prism.parsePropertiesString(mdpGen, "Rmax=?[F \"target\"]");
			mc.setModulesFileAndPropertiesFile(mdpGen, propertiesFile);
			result = mc.check(mdp, propertiesFile.getProperty(0));
			System.out.println(result.getResult());*/

			// Load the adversary back in and export dot
			prism.setEngine(Prism.HYBRID);
			prism.loadModelFromExplicitFiles(new File("adv.sta"), new File("adv.tra"), new File("adv.lab"), null, ModelType.DTMC);
			prism.exportTransToFile(true, Prism.EXPORT_DOT_STATES, new File("adv.dot"));
			
			// Close down
			prism.closeDown();
		}
		catch (FileNotFoundException e) {
			System.out.println("Error: " + e.getMessage());
			System.exit(1);
		}
		catch (PrismException e) {
			System.out.println("Error: " + e.getMessage());
			System.exit(1);
		}
	}

	class MDPGenerator extends DefaultModelGenerator
	{
		// Size of grid
		private int size;
		// Current state being explored (1<=x<=n; 1<=y<=n)
		private State exploreState;
		private int x;
		private int y;
		// Labels for 4 actions
		private String actions[] = { "north", "east", "south", "west" };

		public MDPGenerator(int size)
		{
			this.size = size;
		}

		// Methods for ModelInfo interface

		@Override
		public ModelType getModelType()
		{
			return ModelType.MDP;
		}

		@Override
		public int getNumVars()
		{
			return 2;
		}

		@Override
		public List<String> getVarNames()
		{
			return Arrays.asList("x", "y");
		}

		@Override
		public List<Type> getVarTypes()
		{
			return Arrays.asList(TypeInt.getInstance(), TypeInt.getInstance());
		}

		@Override
		public int getNumLabels()
		{
			return 1;
		};

		@Override
		public List<String> getLabelNames()
		{
			return Arrays.asList("target");
		}
		
		@Override
		public List<String> getRewardStructNames()
		{
			return Arrays.asList("r");
		}
		
		
		// Methods for ModelGenerator interface

		@Override
		public State getInitialState() throws PrismException
		{
			// Initially (x,y) = (1,1)
			return new State(2).setValue(0, 1).setValue(1, 1);
		}

		@Override
		public void exploreState(State exploreState) throws PrismException
		{
			this.exploreState = exploreState;
			x = ((Integer) exploreState.varValues[0]).intValue();
			y = ((Integer) exploreState.varValues[1]).intValue();
		}

		@Override
		public State getExploreState()
		{
			return exploreState;
		}

		@Override
		public int getNumChoices() throws PrismException
		{
			return 4;
		}

		@Override
		public int getNumTransitions(int i) throws PrismException
		{
			return 1;
		}

		@Override
		public Object getTransitionAction(int i) throws PrismException
		{
			return actions[i];
		}

		@Override
		public Object getTransitionAction(int i, int offset) throws PrismException
		{
			return actions[i];
		}

		@Override
		public double getTransitionProbability(int i, int offset) throws PrismException
		{
			return 1;
		}

		@Override
		public State computeTransitionTarget(int i, int offset) throws PrismException
		{
			State target = new State(exploreState);
			switch (i) {
			case 0:
				// North
				target.setValue(1, y < size ? y + 1 : y);
				return target;
			case 1:
				// East
				target.setValue(0, x < size ? x + 1 : x);
				return target;
			case 2:
				// South
				target.setValue(1, y > 1 ? y - 1 : y);
				return target;
			case 3:
				// West
				target.setValue(0, x > 1 ? x - 1 : x);
				return target;
			}
			// Never happens:
			return target;
		}

		@Override
		public boolean isLabelTrue(int i) throws PrismException
		{
			switch (i) {
			case 0:
				// "target"
				return x == size && y == size;
			default:
				throw new PrismException("Label number \"" + i + "\" not defined");
			}
		}

		@Override
		public double getStateReward(int r, State state) throws PrismException
		{
			return 0.0;
		}
		
		@Override
		public double getStateActionReward(int r, State state, Object action) throws PrismException
		{
			return 1.0;
		}
		
		@Override
		public VarList createVarList()
		{
			VarList varList = new VarList();
			try {
				varList.addVar(new Declaration("x", new DeclarationInt(Expression.Int(1), Expression.Int(size))), 0, null);
				varList.addVar(new Declaration("y", new DeclarationInt(Expression.Int(1), Expression.Int(size))), 0, null);
			} catch (PrismLangException e) {
			}
			return varList;
		}
	}
}
