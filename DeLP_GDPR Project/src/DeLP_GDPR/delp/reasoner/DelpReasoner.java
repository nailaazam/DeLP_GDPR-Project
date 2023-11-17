package DeLP_GDPR.delp.reasoner;

import org.tweetyproject.commons.Reasoner;

import DeLP_GDPR.commons.util.rules.Derivation;
import DeLP_GDPR.delp.semantics.ComparisonCriterion;
import DeLP_GDPR.delp.semantics.DelpAnswer;
import DeLP_GDPR.delp.semantics.DialecticalTree;
import DeLP_GDPR.delp.semantics.EmptyCriterion;
import DeLP_GDPR.delp.semantics.DelpAnswer.Type;
import DeLP_GDPR.delp.syntax.DefeasibleLogicProgram;
import DeLP_GDPR.delp.syntax.DefeasibleRule;
import DeLP_GDPR.delp.syntax.DelpArgument;
import DeLP_GDPR.delp.syntax.DelpRule;
import DeLP_GDPR.logics.fol.syntax.FolFormula;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * This reasoner performs default dialectical reasoning
 * on some given DeLP.
 *
 */
public class DelpReasoner implements Reasoner<DelpAnswer.Type,DefeasibleLogicProgram,FolFormula> {

	/**
	 * The comparison criterion is initialized with the "empty criterion"
	 * 
	 * comparisonCriterion: This variable holds the comparison criterion 
	 * used for inference. It is initially set to an instance of EmptyCriterion
	 *  (a default criterion) but can be customized through the constructor.
	 * 
	 */
	private ComparisonCriterion comparisonCriterion = new EmptyCriterion();
	

	/**
	 * Creates a new DelpReasoner for the given delp.	 * 
	 * @param comparisonCriterion a comparison criterion used for inference
	 */
	

	/**The constructor initializes the reasoner with a specified comparison criterion.*/
	public DelpReasoner(ComparisonCriterion comparisonCriterion) {
		this.comparisonCriterion = comparisonCriterion;
		
	}

	/**
	 * This method returns the comparison criterion used in the reasoner.
	 * @return the comparison criterion used in this program
	 */
	public ComparisonCriterion getComparisonCriterion() {
		return comparisonCriterion;
	}
	

	/**
	 * Computes the subset of the arguments of this program, that are warrants.
	 * @param delp a delp
	 * @return a set of <code>DelpArgument</code> that are warrants
	 */
	
	/**This is the method signature. It declares a public method named 
	 * getWarrants that takes a DefeasibleLogicProgram parameter delp and returns a Set of DelpArgument.*/
    public Set<DelpArgument> getWarrants(DefeasibleLogicProgram delp){
    	// Ground the defeasible logic program
    	/**It creates a new DefeasibleLogicProgram called groundDelp by grounding the input delp.*/
    	DefeasibleLogicProgram groundDelp = delp.ground();
    	// Get all arguments from the grounded defeasible logic program
    	/**It retrieves all arguments from the grounded defeasible logic program and stores them in a set called all_arguments.*/
        Set<DelpArgument> all_arguments = groundDelp.ground().getArguments();
     // Use stream to filter and collect warranted arguments
        /**It converts the set of arguments into a stream, which allows for functional-style processing of elements.*/
		return all_arguments.stream()
				/**It applies a filter operation to the stream, keeping only those arguments for which the isWarrant
				 *  method returns true. The isWarrant method checks if an argument is a warrant.*/
                .filter(argument -> isWarrant(groundDelp,argument))
                //It collects the filtered arguments into a new Set using the toSet() collector.
                .collect(Collectors.toSet());
	}

	/**
	 * Checks whether the given argument is a warrant regarding a given set of arguments
	 * @param groundDelp a grounded DeLP
	 * @param argument a DeLP argument
	 * 
	 * @return <source>true</source> iff <source>argument</source> is a warrant given <source>arguments</source>.
	 */
	private boolean isWarrant(DefeasibleLogicProgram groundDelp, DelpArgument argument){
		// Step 1: Create a new DialecticalTree with the given argument
		//Create a new DialecticalTree object with the given argument.
		DialecticalTree dtree = new DialecticalTree(argument);
		// Step 2: Initialize a stack for tree traversal
		// Initialize a stack (Deque) and add the initial DialecticalTree to it.
		Deque<DialecticalTree> stack = new ArrayDeque<>();
		stack.add(dtree);
		// Step 3: Perform tree traversal until the stack is empty
		/**Perform tree traversal using a while loop until the stack is empty.
		Pop the top element (dtree2) from the stack.
		Add all defeaters of the popped element to the stack.*/
		while(!stack.isEmpty()){
			// Step 4: Pop the top element from the stack
			DialecticalTree dtree2 = stack.pop();
			// Step 5: Add all defeaters of the popped element to the stack
			stack.addAll(dtree2.getDefeaters(groundDelp,comparisonCriterion));
		}
		// Step 6: Check if the marking of the original DialecticalTree is UNDEFEATED
		/** The method returns true if the marking is UNDEFEATED, indicating that the argument is a warrant, and false otherwise.*/
		return dtree.getMarking().equals(DialecticalTree.Mark.UNDEFEATED);
	}
	
	/**
	 * Returns all arguments with the given conclusion from the delp.
	 * @param delp some delp.
	 * @param f a formula
	 * @return all arguments with the given conclusion from the delp.
	 * 
	 * The primary purpose of this method is to identify and return
	 *  minimal arguments that, together with their associated rules, 
	 *  collectively support a specified conclusion within a defeasible logic program
	 */
	public static Set<DelpArgument> getArgumentsWithConclusion(DefeasibleLogicProgram delp, FolFormula f){
		// Step 1: Create a set to store all rules
		/**Create a collection to store all defeasible rules (allRules).
		Populate allRules with rules from the defeasible logic program (delp).
		Generate all derivations (allDerivations) for the given formula (f).*/
		Collection<DelpRule> allRules = new HashSet<DelpRule>();
		allRules.addAll(delp);
		// Step 2: Generate all derivations for the given formula
		/**Create a set (arguments) to store DelpArgument objects.
		Iterate through each derivation.*/
		Set<Derivation<DelpRule>> allDerivations = Derivation.allDerivations(allRules, f);
		// Step 3: Create a set to store DelpArguments
		Set<DelpArgument> arguments = new HashSet<>();
		// Step 4: Iterate through each derivation. Iterate through each derivation.
		
		for(Derivation<DelpRule> derivation: allDerivations){
			// Step 5: Extract defeasible rules from the derivation
			Set<DefeasibleRule> rules = derivation.stream()
                    .filter(rule -> rule instanceof DefeasibleRule)
                    .map(rule -> (DefeasibleRule) rule)
                    .collect(Collectors.toSet());
			// Step 6: Consistency check - rules must be consistent with the strict knowledge part
			if(delp.isConsistent(rules))
				// Step 7: Add a new DelpArgument to the set with the conclusion of the derivation
				arguments.add(new DelpArgument(rules,(FolFormula)derivation.getConclusion()));
		}
		// Step 8: Subargument test - filter out non-minimal arguments
		Set<DelpArgument> result = new HashSet<>();
		for(DelpArgument argument1: arguments){
			boolean is_minimal = true;
			for(DelpArgument argument2: arguments){
				// Step 9: Check if argument1 is a strong subargument of argument2
				if(argument1.getConclusion().equals(argument2.getConclusion()) && argument2.isStrongSubargumentOf(argument1)){
					is_minimal = false;
					break;
				}
			}
			// Step 10: If argument1 is minimal, add it to the result set
			if(is_minimal) result.add(argument1);
		}
		// Step 11: Return the set of minimal arguments with the given conclusion
		return result;
	}

	/* (non-Javadoc)
	 * @see org.tweetyproject.commons.Reasoner#query(org.tweetyproject.commons.BeliefBase, org.tweetyproject.commons.Formula)
	 */
	@Override
	public Type query(DefeasibleLogicProgram delp, FolFormula f) {
		// check query:	
		// Verifies that the formula (f) is a literal and is ground. If not, it throws an exception.
		if(!f.isLiteral())
			throw new IllegalArgumentException("Formula is expected to be a literal: "+f);
		if(!f.isGround())
			throw new IllegalArgumentException("Formula is expected to be ground: "+f);
		// Ground the Defeasible Logic Program:
		// Creates a grounded version of the defeasible logic program
		DefeasibleLogicProgram groundDelp = delp.ground();
		// Initialize Variables:
		//nitializes a boolean variable (warrant) to track whether there is a warrant for the formula.
		//Retrieves all arguments that support the formula (f) using the getArgumentsWithConclusion method.
		boolean warrant = false;		
		Set<DelpArgument> args = getArgumentsWithConclusion(groundDelp, f);
		// Process Arguments Supporting f:
		// For each argument (arg) supporting the formula (f), creates a dialectical tree (dtree) rooted at that argument.
		for(DelpArgument arg: args){			
			DialecticalTree dtree = new DialecticalTree(arg);
			//Uses a stack-based approach to traverse the dialectical tree and compute defeaters at each node.
			Deque<DialecticalTree> stack = new ArrayDeque<>();
			stack.add(dtree);
			while(!stack.isEmpty()){
				DialecticalTree dtree2 = stack.pop();
				stack.addAll(dtree2.getDefeaters(groundDelp,comparisonCriterion));
				//inferenceSteps++;
			}
			// If the marking of the root (dtree) is UNDEFEATED, sets warrant to true and breaks the loop
			if(dtree.getMarking().equals(DialecticalTree.Mark.UNDEFEATED)){
				warrant = true;
				break;
			}
			 
		}
		// get all arguments for ~f (if f is not already warranted)
		// Initialize comp_warrant: 
		// Initializes a boolean variable comp_warrant to track whether there is a warrant for the complement of the formula.
		boolean comp_warrant = false;
		//Check if warrant is false:
		//Checks if the boolean variable warrant is false. If warrant is true, the code inside the block is skipped.
		if(!warrant){		
			// Retrieves all arguments that support the complement of the formula 
			args = getArgumentsWithConclusion(groundDelp, (FolFormula) f.complement());
			// Process Arguments Supporting the Complement Formula:
			//For each argument (arg) supporting the complement of the formula, creates a dialectical tree (dtree) rooted at that argument.
			for(DelpArgument arg: args){
				DialecticalTree dtree = new DialecticalTree(arg);
				//Uses a stack-based approach to traverse the dialectical tree and compute defeaters at each node.
				Deque<DialecticalTree> stack = new ArrayDeque<>();
				stack.add(dtree);
				while(!stack.isEmpty()){
					DialecticalTree dtree2 = stack.pop();
					stack.addAll(dtree2.getDefeaters(groundDelp,comparisonCriterion));
					//inferenceSteps++; 
				}
				// If the marking of the root (dtree) is UNDEFEATED, sets comp_warrant to true and breaks the loop.
				if(dtree.getMarking().equals(DialecticalTree.Mark.UNDEFEATED)){
					comp_warrant = true;
					break;
				}
				//inferenceSteps++;
			}
		}		
		if(warrant){
			// System.out.println("Inference Steps: " + inferenceSteps);
			return Type.YES;
		}else if(comp_warrant){
			//System.out.println("Inference Steps: " + inferenceSteps);
			return Type.NO;
		}else{
			//System.out.println("Inference Steps: " + inferenceSteps);
			return Type.UNDECIDED;
		}		
	}	
	
	public boolean isInstalled() {
		return true;
	}
}
