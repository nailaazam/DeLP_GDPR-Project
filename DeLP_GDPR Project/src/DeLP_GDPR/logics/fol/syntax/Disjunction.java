package DeLP_GDPR.logics.fol.syntax;



import java.util.Collection;

import java.util.HashSet;

import DeLP_GDPR.logics.common.LogicalSymbols;
import DeLP_GDPR.logics.commons.syntax.RelationalFormula;

/**
 * The classical disjunction of first-order logic.
 */
public class Disjunction extends AssociativeFolFormula{
	
	/**
	 * Creates a new disjunction with the given inner formulas. 
	 * @param formulas a collection of formulas.
	 */
	public Disjunction(Collection<? extends RelationalFormula> formulas){
		super(formulas);
	}
	
	/**
	 * Creates a new (empty) disjunction.
	 */
	public Disjunction(){
		this(new HashSet<RelationalFormula>());
	}
	
	/**
	 * Creates a new disjunction with the two given formulae
	 * @param first a relational formula.
	 * @param second a relational formula.
	 */
	public Disjunction(RelationalFormula first, RelationalFormula second){
		this();
		this.add(first);
		this.add(second);
	}	
	

	@Override
	public boolean isDnf(){
		for(RelationalFormula f: this)
			if(!((FolFormula)f).isDnf() && !(f instanceof Disjunction)) return false;
		return true;
	}
	
		
  @Override
  public FolFormula toNnf() {
    Disjunction d = new Disjunction();
    for(RelationalFormula p : this) {
      if(p instanceof FolFormula)
        d.add( ((FolFormula) p).toNnf() );
      else
        throw new IllegalStateException("Can not convert conjunctions containing non-first-order formulae to NNF.");
    }
    return d;
  }
  
  @Override
  public RelationalFormula collapseAssociativeFormulas() {
    if(this.isEmpty())
      return new Contradiction();
    if(this.size() == 1)
      return ((FolFormula)this.iterator().next()).collapseAssociativeFormulas();
    Disjunction newMe = new Disjunction();
    for(RelationalFormula f: this){
      if(! (f instanceof FolFormula)) throw new IllegalStateException("Can not collapse disjunctions containing non-first-order formulae.");
      RelationalFormula newF = ((FolFormula)f).collapseAssociativeFormulas();
      if(newF instanceof Disjunction)
        newMe.addAll((Disjunction) newF);
      else newMe.add(newF);
    }
    return newMe;
  }
	
	@Override
	public Disjunction clone() {
		return new Disjunction(support.copyHelper(this));
	}
	
	//-------------------------------------------------------------------------
	//	ASSOC SUPPORT BRIDGE METHODS
	//-------------------------------------------------------------------------

	@SuppressWarnings("unchecked")
	@Override
	public Disjunction createEmptyFormula() {
		return new Disjunction();
	}

	@Override
	public String getOperatorSymbol() {
		return LogicalSymbols.DISJUNCTION();
	}

	@Override
	public String getEmptySymbol() {
		return LogicalSymbols.CONTRADICTION();
	}
}
