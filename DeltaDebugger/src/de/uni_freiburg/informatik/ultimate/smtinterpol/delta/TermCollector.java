/*
 * Copyright (C) 2012-2013 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.delta;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class TermCollector extends NonRecursive {
	
	private final class DepthWalker extends TermWalker {
		
		private final int mDepth;

		public DepthWalker(Term term, int depth) {
			super(term);
			mDepth = depth;
		}
		
		private boolean isReplaceable(Term t) {
			return !(t instanceof ConstantTerm) 
					&& t != t.getTheory().mTrue && t != t.getTheory().mFalse;
		}

		@Override
		public void walk(NonRecursive walker) {
			Term t = getTerm();
			if (mDepth == TermCollector.this.mDepth && isReplaceable(t))
				mTerms.add(t);
			else
				super.walk(walker);
		}

		@Override
		public void walk(NonRecursive walker, ConstantTerm term) {
			// Already a leaf
		}

		@Override
		public void walk(NonRecursive walker, AnnotatedTerm term) {
			walker.enqueueWalker(
					new DepthWalker(term.getSubterm(), mDepth + 1));
		}

		@Override
		public void walk(NonRecursive walker, ApplicationTerm term) {
			for (Term p : term.getParameters())
				walker.enqueueWalker(new DepthWalker(p, mDepth + 1));
		}

		@Override
		public void walk(NonRecursive walker, LetTerm term) {
			for (Term v : term.getValues())
				walker.enqueueWalker(new DepthWalker(v, mDepth + 1));
			walker.enqueueWalker(
					new DepthWalker(term.getSubTerm(), mDepth + 1));
		}

		@Override
		public void walk(NonRecursive walker, QuantifiedFormula term) {
			walker.enqueueWalker(
					new DepthWalker(term.getSubformula(), mDepth + 1));
		}

		@Override
		public void walk(NonRecursive walker, TermVariable term) {
			// Already a leaf
		}
		
	}

	private final int mDepth;
	private final List<Term> mTerms;
	
	public TermCollector(int depth) {
		mDepth = depth;
		mTerms = new ArrayList<Term>();
	}
	
	public void add(Term t) {
		run(new DepthWalker(t, 0));
	}
	
	public List<Term> getTerms() {
		return mTerms;
	}

}
