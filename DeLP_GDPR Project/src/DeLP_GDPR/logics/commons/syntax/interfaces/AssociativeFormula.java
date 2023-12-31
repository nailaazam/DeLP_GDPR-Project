package DeLP_GDPR.logics.commons.syntax.interfaces;



import java.util.List;
import java.util.Set;

/**
 * This interfaces describes associative formulas like a disjunction or
 * a conjunction.
 * @param <T> the type of formulas
 */
public interface AssociativeFormula<T extends SimpleLogicalFormula> 
	extends SimpleLogicalFormula, List<T> {
	
	/** @return all the formulas saved as childs in the associative formula */
	List<T> getFormulas();
	
	/**
	 * Process the formulas of type C that are children of this associative
	 * formula
	 * @param cls	the class structure defining the type of formulas which
	 * 				are searched.
	 * @return		A set of formulas of type C which are members of the associative formula
	 * @param <C> the type of formulas
	 */
	<C extends SimpleLogicalFormula> Set<C> getFormulas(Class<C> cls);
}
