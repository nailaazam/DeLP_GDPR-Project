package DeLP_GDPR.logics.fol.syntax;



import java.util.Set;

import DeLP_GDPR.logics.commons.syntax.Functor;
import DeLP_GDPR.logics.commons.syntax.LogicalSymbols;
import DeLP_GDPR.logics.commons.syntax.Predicate;
import DeLP_GDPR.logics.commons.syntax.RelationalFormula;
import DeLP_GDPR.logics.commons.syntax.Variable;
import DeLP_GDPR.logics.commons.syntax.interfaces.Term;

/**
 * The classical negation of first-order logic.
 */
public class Negation extends FolFormula {
	
	private FolFormula folFormula;
	/**
	 * 
	 * @param formula relational formula to be negated
	 */
	public Negation(RelationalFormula formula){
		if(!formula.isWellFormed())
			throw new IllegalArgumentException("FolFormula not well-formed.");		
		this.folFormula = (FolFormula)formula;		
	}
	
	@Override
	public FolFormula getFormula(){
		return this.folFormula;
	}
	
	
	@Override
	public Set<? extends Predicate> getPredicates(){
		return this.folFormula.getPredicates();
	}
	
	
	@Override
	public Set<Functor> getFunctors(){
		return this.folFormula.getFunctors();
	}
	
	
	@SuppressWarnings("unchecked")
	@Override
	public Set<FolAtom> getAtoms(){
		return (Set<FolAtom>) this.folFormula.getAtoms();
	}
	
	@Override
	public boolean containsQuantifier(){
		return this.folFormula.containsQuantifier();
	}
	
	
	@Override
	public boolean isClosed(){
		return this.folFormula.isClosed();
	}
		
	
	@Override
	public Negation substitute(Term<?> v, Term<?> t) throws IllegalArgumentException {
		return new Negation(this.folFormula.substitute(v, t));
	}
	
	
	@Override
	public boolean isClosed(Set<Variable> boundVariables){
		return this.folFormula.isClosed(boundVariables);
	}
	
	@Override
	public Set<Variable> getUnboundVariables(){
		//return this.getTerms(Variable.class);
		return folFormula.getUnboundVariables();
	}
	
	
	@Override
	public boolean isWellBound(){
		return this.folFormula.isWellBound();
	}
	
	
	@Override
	public boolean isWellBound(Set<Variable> boundVariables){
		return this.folFormula.isWellBound(boundVariables);
	}
	
	
	@Override
	public boolean isLiteral(){
		return (this.folFormula instanceof FolAtom);
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString(){
		return LogicalSymbols.CLASSICAL_NEGATION() + this.folFormula;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((folFormula == null) ? 0 : folFormula.hashCode());
		return result;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		Negation other = (Negation) obj;
		if (folFormula == null) {
			if (other.folFormula != null)
				return false;
		} else if (!folFormula.equals(other.folFormula))
			return false;
		return true;
	}

	

	
	@Override
	public boolean isDnf() {
		return (this.folFormula instanceof FolAtom);
	}
	
	
	@Override
	public FolFormula toNnf() {
    // remove double negation    
    if(folFormula instanceof Negation)
      return ((Negation)folFormula).folFormula.toNnf();

     // Distribute negation inside conjunctions or disjunctions according to deMorgan's laws:
     // -(p & q)  = -p || -q
     // -(p || q) = -p & -q
    if(folFormula instanceof Conjunction) {
      Conjunction c = (Conjunction)folFormula;
      Disjunction d = new Disjunction();
      
      for(RelationalFormula p : c) {
        d.add( new Negation( p ).toNnf() );
      }
      return d;
    }
    if(folFormula instanceof Disjunction) {
       Disjunction d = (Disjunction)folFormula;
       Conjunction c = new Conjunction();
       
       for(RelationalFormula p : d) {
         c.add( new Negation( p ).toNnf() );
       }
       return c;
    }
    
    // Distribute negation inside quantifiers:
    // NNF(! FORALL x : R(x)) = EXISTS x : NNF( ! R(x) )
    if(folFormula instanceof ForallQuantifiedFormula) {
      ForallQuantifiedFormula q = (ForallQuantifiedFormula) folFormula;
      return new ExistsQuantifiedFormula( new Negation(q.getFormula()).toNnf(), q.getQuantifierVariables() );
    }
    // NNF(! EXISTS x : R(x)) = FORALL x : NNF( ! R(x) )
    if(folFormula instanceof ExistsQuantifiedFormula) {
      ExistsQuantifiedFormula q = (ExistsQuantifiedFormula) folFormula;
      return new ForallQuantifiedFormula( new Negation(q.getFormula()).toNnf(), q.getQuantifierVariables() );
    }
    if(folFormula instanceof Tautology)
      return new Contradiction();
    if(folFormula instanceof Contradiction)
      return new Tautology();
    
    return new Negation(this.folFormula.toNnf());
	}
	
	
	@Override
	public FolFormula collapseAssociativeFormulas() {
	  return new Negation( folFormula.collapseAssociativeFormulas() );
	}

	@Override
	public Set<Term<?>> getTerms() {
		return folFormula.getTerms();
	}

	@Override
	public <C extends Term<?>> Set<C> getTerms(Class<C> cls) {
		return folFormula.getTerms(cls);
	}

	@Override
	public Negation clone() {
		return new Negation(this.getFormula().clone());
	}
}