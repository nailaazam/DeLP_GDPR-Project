package DeLP_GDPR.dung.ldo.syntax;




import java.util.HashSet;
import java.util.Set;

import DeLP_GDPR.logics.pl.syntax.PlPredicate;

/**
 * Creates a relational formula, i.e. "A -&gt; B" that can be used to model attacks in LDO.
 */
public class LdoRelation extends LdoFormula {

	private LdoFormula left;
	private LdoFormula right;
	
	
	/**
	 * 
	 * @param left left
	 * @param right right
	 */
	public LdoRelation(LdoFormula left, LdoFormula right){
		this.left = left;
		this.right = right;
	}
	
	
	/**
	 * 
	 * @return return
	 */
	
	public LdoFormula getLeft(){
		return this.left;
	}
	
	
	/**
	 * 
	 * @return return
	 */
	public LdoFormula getRight(){
		return this.right;
	}

	/* (non-Javadoc)
	 * @see DeLP_GDPR.dung.ldo.syntax.LdoFormula#getAtoms()
	 */
	@Override
	public Set<LdoArgument> getAtoms() {
		Set<LdoArgument> result = new HashSet<LdoArgument>();
		result.addAll(this.left.getAtoms());
		result.addAll(this.right.getAtoms());
		return result;
	}

	/* (non-Javadoc)
	 * @see DeLP_GDPR.dung.ldo.syntax.LdoFormula#getPredicates()
	 */
	@Override
	public Set<PlPredicate> getPredicates() {
		Set<PlPredicate> result = new HashSet<PlPredicate>();
		result.addAll(this.left.getPredicates());
		result.addAll(this.right.getPredicates());
		return result;
	}

	/* (non-Javadoc)
	 * @see DeLP_GDPR.dung.ldo.syntax.LdoFormula#getLiterals()
	 */
	@Override
	public Set<LdoFormula> getLiterals() {
		Set<LdoFormula> result = new HashSet<LdoFormula>();
		result.addAll(this.left.getLiterals());
		result.addAll(this.right.getLiterals());
		return result;
	}

	/* (non-Javadoc)
	 * @see DeLP_GDPR.dung.ldo.syntax.LdoFormula#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((left == null) ? 0 : left.hashCode());
		result = prime * result + ((right == null) ? 0 : right.hashCode());
		return result;
	}

	/* (non-Javadoc)
	 * @see DeLP_GDPR.dung.ldo.syntax.LdoFormula#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		LdoRelation other = (LdoRelation) obj;
		if (left == null) {
			if (other.left != null)
				return false;
		} else if (!left.equals(other.left))
			return false;
		if (right == null) {
			if (other.right != null)
				return false;
		} else if (!right.equals(other.right))
			return false;
		return true;
	}

	/* (non-Javadoc)
	 * @see DeLP_GDPR.dung.ldo.syntax.LdoFormula#clone()
	 */
	@Override
	public LdoFormula clone() {
		return new LdoRelation(this.left,this.right);
	}
	
	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	public String toString(){
		return this.left.toString() + "->" + this.right.toString(); 
	}
}