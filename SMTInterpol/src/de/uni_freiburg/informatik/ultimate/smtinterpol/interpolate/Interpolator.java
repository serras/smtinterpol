/*
 * Copyright (C) 2009-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collection;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.logic.AnnotatedTerm;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;
import de.uni_freiburg.informatik.ultimate.smtinterpol.LogProxy;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ProofConstants;
import de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2.TerminationRequest;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;

/**
 * This interpolator computes the interpolants of a refutation for the partitions specified by the user. It works in a
 * non-recursive way on the proof tree generated during SMT solving.
 *
 * @author Jochen Hoenicke, Tanja Schindler
 */
public class Interpolator extends NonRecursive {

	/**
	 * The name of the auxiliary EQ predicate used for CC interpolation.
	 */
	public static final String EQ = "@EQ";

	private final TerminationRequest mCancel;

	InterpolantChecker mChecker;

	LogProxy mLogger;
	Theory mTheory;
	int mNumInterpolants;

	Occurrence mFullOccurrence;

	/**
	 * Array encoding the tree-structure for tree interpolants. The interpolants are always required to be in post-order
	 * tree traversal. The i-th element of this array contains the lowest index occuring in the sub-tree with the i-th
	 * element as root node. This is the index of the lower left-most node in the sub-tree. The nodes between
	 * m_startOfSubtrees[i] and i form the sub-tree with the root i. To traverse the children of a node the following
	 * pattern can be used:
	 *
	 * <pre>
	 * for (int child = node-1; child >= m_startOfSubtrees[node];
	 *      child = m_startOfSubtrees[child] - 1) {
	 *      ...
	 * }
	 * </pre>
	 *
	 * To find the parent of a node do:
	 *
	 * <pre>
	 * int parent = node + 1;
	 * while (m_startOfSubtrees[parent] > node)
	 * 	parent++;
	 * </pre>
	 */
	int[] mStartOfSubtrees;
	HashMap<Term, Occurrence> mSymbolPartition;
	HashMap<String, Integer> mPartitions;
	HashMap<Term, LitInfo> mAtomOccurenceInfos;
	HashMap<Term, Term[]> mInterpolants;
	HashMap<Term, InterpolatorClauseTermInfo> mClauseTermInfos;
	HashMap<Term, InterpolatorAtomInfo> mLiteralTermInfos;
	HashMap<String, Occurrence> mSymbolOccurrenceInfos;
	HashMap<Term, TermVariable> mMixedTermAuxEq;

	/**
	 * The interpolants which have already been computed. Used to store the interpolants preceding a resolution before
	 * combining them. In the end of the interpolation, it contains only the interpolants for the refutation,
	 * corresponding to the specified partitions.
	 */
	private final ArrayDeque<Term[]> mInterpolated = new ArrayDeque<>();

	/**
	 * This class goes through the proof terms of the proof tree for the input clause. It checks if the interpolant for
	 * a term already exists, and if not, it enqueues new walkers depending on the node type.
	 *
	 * @param proofTerm
	 *            the proof term to interpolate
	 */
	public static class ProofTreeWalker implements Walker {
		private final Term mProofTerm;

		public ProofTreeWalker(final Term proofTerm) {
			mProofTerm = proofTerm;
		}

		@Override
		public void walk(final NonRecursive engine) {
			final Interpolator proofTreeWalker = (Interpolator) engine;
			if (proofTreeWalker.checkCacheForInterpolants(mProofTerm)) {
				return;
			}
			final InterpolatorClauseTermInfo proofTermInfo = ((Interpolator) engine).getClauseTermInfo(mProofTerm);
			if (proofTermInfo.isResolution()) {
				((Interpolator) engine).walkResolutionNode(mProofTerm);
			} else {
				((Interpolator) engine).walkLeafNode(mProofTerm);
			}
		}
	}

	/**
	 * This class combines the interpolants preceding a resolution step and adds the interpolant of the resolvent to the
	 * Interpolated stack.
	 *
	 * @param the
	 *            pivot of the resolution step
	 */
	public static class CombineInterpolants implements Walker {
		private final Term mPivot;

		public CombineInterpolants(final Term pivot) {
			mPivot = pivot;
		}

		@Override
		public void walk(final NonRecursive engine) {
			((Interpolator) engine).combine(mPivot);
		}
	}

	/**
	 * This class summarizes a hyper-resolution step by adding the interpolants to the cache, checking for inductivity,
	 * and providing debug messages.
	 */
	public static class SummarizeResolution implements Walker {
		private final Term mProofTerm;

		public SummarizeResolution(final Term proofTerm) {
			mProofTerm = proofTerm;
		}

		@Override
		public void walk(final NonRecursive engine) {
			((Interpolator) engine).summarize(mProofTerm);
		}
	}

	public Interpolator(final LogProxy logger, final Script checkingSolver, final Collection<Term> allAssertions,
			final Theory theory, final Set<String>[] partitions, final int[] startOfSubTrees,
			final TerminationRequest cancel) {
		assert partitions.length == startOfSubTrees.length;
		mPartitions = new HashMap<>();
		for (int i = 0; i < partitions.length; i++) {
			final Integer part = i;
			for (final String name : partitions[i]) {
				mPartitions.put(name, part);
			}
		}
		mLogger = logger;
		mCancel = cancel;
		if (checkingSolver != null) {
			mChecker = new InterpolantChecker(this, checkingSolver);
			mChecker.assertUnpartitionedFormulas(allAssertions, mPartitions.keySet());
		}
		mTheory = theory;
		mNumInterpolants = partitions.length - 1;
		mFullOccurrence = new Occurrence();
		mFullOccurrence.occursIn(-1);

		mStartOfSubtrees = startOfSubTrees;
		mSymbolPartition = new HashMap<>();
		mAtomOccurenceInfos = new HashMap<>();
		mInterpolants = new HashMap<>();
		mClauseTermInfos = new HashMap<>();
		mLiteralTermInfos = new HashMap<>();
		mSymbolOccurrenceInfos = new HashMap<>();
		mMixedTermAuxEq = new HashMap<>();
	}

	public LogProxy getLogger() {
		return mLogger;
	}

	public Term[] getInterpolants(final Term proofTree) {
		colorLiterals(proofTree);
		final Term[] interpolants = interpolate(proofTree);
		for (int i = 0; i < interpolants.length; i++) {
			interpolants[i] = unfoldLAs(interpolants[i]);
		}
		if (mChecker != null) {
			if (!mChecker.checkFinalInterpolants(mPartitions, interpolants)) {
				throw new SMTLIBException("generated interpolants did not pass sanity check");
			}
		}
		return interpolants;
	}

	public Term[] interpolate(final Term proofTerm) {
		if (mInterpolants.containsKey(proofTerm)) {
			mLogger.debug("Proof term %s has been interpolated before.", proofTerm.hashCode());
			return mInterpolants.get(proofTerm);
		}
		if (mCancel.isTerminationRequested()) {
			throw new SMTLIBException("Timeout exceeded");
		}

		Term[] interpolants = null;

		run(new ProofTreeWalker(proofTerm));

		// collect the final interpolants from the Interpolated stack
		interpolants = collectInterpolated();
		return interpolants;
	}

	/**
	 * Enqueue walkers for the single steps in a hyper-resolution step.
	 *
	 * @param clause
	 *            the resolvent clause
	 */
	private void walkResolutionNode(final Term proofTerm) {
		if (mCancel.isTerminationRequested()) {
			throw new SMTLIBException("Timeout exceeded");
		}
		final InterpolatorClauseTermInfo proofTermInfo = getClauseTermInfo(proofTerm);
		// get primary and antecedents
		final Term prim = proofTermInfo.getPrimary();

		final AnnotatedTerm[] antecedents = proofTermInfo.getAntecedents();

		enqueueWalker(new SummarizeResolution(proofTerm));
		// enqueue walkers for primary and antecedents in reverse order
		// alternating with Combine walkers
		for (int i = antecedents.length - 1; i >= 0; i--) {
			final Term pivot = (Term) antecedents[i].getAnnotations()[0].getValue();
			final Term antecedent = antecedents[i].getSubterm();

			enqueueWalker(new CombineInterpolants(pivot));
			enqueueWalker(new ProofTreeWalker(antecedent));
		}
		enqueueWalker(new ProofTreeWalker(prim));
	}

	/**
	 * Interpolate a proof tree leaf depending on its type.
	 *
	 * @param clause
	 *            the clause to interpolate
	 */
	@SuppressWarnings("unused")
	private void walkLeafNode(final Term leaf) {
		if (mCancel.isTerminationRequested()) {
			throw new SMTLIBException("Timeout exceeded");
		}
		Term[] interpolants;
		final InterpolatorClauseTermInfo leafTermInfo = getClauseTermInfo(leaf);
		if (leafTermInfo.getLeafKind().equals(ProofConstants.FN_CLAUSE)) {
			final String source = leafTermInfo.getSource();
			final int partition = mPartitions.containsKey(source) ? mPartitions.get(source) : 0;
			interpolants = new Term[mNumInterpolants];
			for (int i = 0; i < mNumInterpolants; i++) {
				interpolants[i] = mStartOfSubtrees[i] <= partition && partition <= i ? mTheory.mFalse : mTheory.mTrue;
			}
		} else if (leafTermInfo.getLeafKind().equals(ProofConstants.FN_LEMMA)) {
			if (leafTermInfo.getLemmaType().equals(":EQ")) {
				interpolants = new EQInterpolator(this).computeInterpolants(leaf);
			} else if (leafTermInfo.getLemmaType().equals(":CC")) {
				final CCInterpolator ipolator = new CCInterpolator(this);
				interpolants = ipolator.computeInterpolants(leaf);
				// Replace non-shared symbols in interpolant.
				interpolants = replaceNonsharedSymbols(interpolants);
			} else if (leafTermInfo.getLemmaType().equals(":LA")) {
				final LAInterpolator ipolator = new LAInterpolator(this);
				interpolants = ipolator.computeInterpolants(leaf);
			} else if (leafTermInfo.getLemmaType().equals(":trichotomy")) {
				final LAInterpolator ipolator = new LAInterpolator(this);
				interpolants = ipolator.computeTrichotomyInterpolants(leaf);
			} else if (leafTermInfo.getLemmaType().equals(":read-over-weakeq")
					|| leafTermInfo.getLemmaType().equals(":weakeq-ext")
					|| leafTermInfo.getLemmaType().equals(":const-weakeq")
					|| leafTermInfo.getLemmaType().equals(":read-const-weakeq")) {
				final ArrayInterpolator ipolator = new ArrayInterpolator(this);
				interpolants = ipolator.computeInterpolants(leaf);
			} else if (leafTermInfo.getLemmaType().equals(":inst")) {
				// TODO: Only supports EUF.
				final CCInterpolator ipolator = new CCInterpolator(this);
				interpolants = ipolator.interpolateInstantiation(leaf);
				// Replace non-shared symbols in interpolant.
				interpolants = replaceNonsharedSymbols(interpolants);
				// Check for unsupported variables and add quantifiers if necessary.
				interpolants = addQuantifier(interpolants, new Term[] { leaf });
			} else {
				throw new UnsupportedOperationException("Unknown lemma type!");
			}
		} else {
			throw new UnsupportedOperationException("Cannot interpolate " + leaf);
		}

		// add the interpolants to the stack and the cache
		mInterpolated.add(interpolants);
		mInterpolants.put(leaf, interpolants);
		mLogger.debug("Interpolating leaf %s %s yields ...", leaf.hashCode(), leaf);
		for (int i = 0; i <= mNumInterpolants - 1; i++) {
			mLogger.debug(interpolants[i]);
		}

		if (Config.DEEP_CHECK_INTERPOLANTS && mChecker != null) {
			mChecker.checkInductivity(leafTermInfo.getLiterals(), interpolants);
		}
	}

	/**
	 * Combine the interpolants preceding a resolution step depending on the type of the pivot.
	 *
	 * @param pivot
	 *            the pivot of the resolution step
	 */
	private void combine(final Term pivot) {
		final Term pivotAtom = getAtom(pivot);
		final InterpolatorAtomInfo pivotTermInfo = getAtomTermInfo(pivotAtom);
		final LitInfo pivInfo = mAtomOccurenceInfos.get(pivotAtom);

		final Term[] antecedentInterp = collectInterpolated();
		final Term[] primInterp = collectInterpolated();
		final Term[] interp = new Term[mNumInterpolants];

		for (int i = 0; i < mNumInterpolants; i++) {
			mLogger.debug("Pivot %3$s%4$s on interpolants %1$s and %2$s gives...", primInterp[i], antecedentInterp[i],
					unquote(pivot), pivInfo);
			if (pivInfo.isALocal(i)) {
				interp[i] = mTheory.or(primInterp[i], antecedentInterp[i]);
			} else if (pivInfo.isBLocal(i)) {
				interp[i] = mTheory.and(primInterp[i], antecedentInterp[i]);
			} else if (pivInfo.isAB(i)) {
				interp[i] = mTheory.ifthenelse(unquote(pivot), primInterp[i], antecedentInterp[i]);
			} else {
				if (pivotTermInfo.isCCEquality() || pivotTermInfo.isLAEquality()) {
					Term eqIpol, neqIpol;
					if (pivot == pivotAtom) {
						// pivot is the "eq" and occurs in antecedent
						eqIpol = antecedentInterp[i];
						neqIpol = primInterp[i];
					} else {
						// pivot is the "neq" and occurs in antecedent
						eqIpol = primInterp[i];
						neqIpol = antecedentInterp[i];
					}
					interp[i] = mixedEqInterpolate(eqIpol, neqIpol, pivInfo.mMixedVar);
				} else if (pivotTermInfo.isBoundConstraint()) {
					interp[i] = mixedPivotLA(antecedentInterp[i], primInterp[i], pivInfo.mMixedVar);
				} else {
					throw new UnsupportedOperationException("Cannot handle mixed literal " + unquote(pivot));
				}
			}
			mLogger.debug(interp[i]);
		}
		// add the interpolants to the Interpolated stack
		mInterpolated.add(interp);
	}

	/**
	 * Summarize the results of a hyper-resolution step. Introduce quantifiers if
	 * necessary.
	 *
	 * @param clause the interpolated clause
	 */
	@SuppressWarnings("unused")
	private void summarize(final Term proofTerm) {
		Term[] interpolants = null;
		interpolants = mInterpolated.getLast();
		final InterpolatorClauseTermInfo proofTermInfo = getClauseTermInfo(proofTerm);
		if (proofTermInfo.getLiterals() == null) {
			proofTermInfo.computeResolutionLiterals(this);
		}

		// Add quantifiers if necessary. TODO: Is there a better place to do this?
		interpolants = addQuantifier(interpolants, proofTermInfo.getLiterals());

		if (Config.DEEP_CHECK_INTERPOLANTS && mChecker != null) {
			mChecker.checkInductivity(proofTermInfo.getLiterals(), interpolants);
		}

		mInterpolants.put(proofTerm, interpolants);
		mLogger.debug("...which is the resulting interpolant for Term %s ", proofTerm.hashCode());

	}

	/**
	 * Get the last interpolant array from the Interpolated stack.
	 */
	protected final Term[] collectInterpolated() {
		return mInterpolated.removeLast();
	}

	/**
	 * Check if a clause has been interpolated before. If so, add the interpolant array to the Interpolated stack.
	 *
	 * @param clause
	 *            the clause to interpolate
	 * @return true iff clause has been interpolated before
	 */
	public boolean checkCacheForInterpolants(final Term proofTerm) {
		final Term[] interpolants = mInterpolants.get(proofTerm);
		if (interpolants != null) {
			// add the interpolant to the interpolated stack
			mInterpolated.add(interpolants);
			return true;
		}
		return false;
	}

	class Occurrence {
		BitSet mInA;
		BitSet mInB;
		BitSet mContainsMixedTerm;

		public Occurrence() {
			mInA = new BitSet(mNumInterpolants + 1);
			mInA.set(mNumInterpolants);
			mInB = new BitSet(mNumInterpolants + 1);
			mContainsMixedTerm = new BitSet(mNumInterpolants + 1);
		}

		public Occurrence(final BitSet inA, final BitSet inB) {
			mInA = inA;
			mInB = inB;
		}

		public Occurrence(final BitSet inA, final BitSet inB, final BitSet containsMixedTerm) {
			mInA = inA;
			mInB = inB;
			mContainsMixedTerm = containsMixedTerm;
		}

		public void occursIn(final int partition) {
			for (int i = 0; i <= mNumInterpolants; i++) {
				if (partition == -1) {
					mInA.set(i);
					if (i != mNumInterpolants) { // All literals are in A in the root
						mInB.set(i);
					}
				} else if (i < partition || mStartOfSubtrees[i] > partition) {
					mInB.set(i);
				} else {
					mInA.set(i);
				}
			}
		}

		public boolean isALocalInSomeChild(final int partition) {
			for (int i = partition - 1; i >= mStartOfSubtrees[partition];) {
				if (mInA.get(i)) {
					return true;
				}
				i = mStartOfSubtrees[i] - 1;
			}
			return false;
		}

		public boolean contains(final int partition) {
			if (partition == -1) {
				for (int i = 0; i <= mNumInterpolants; i++) {
					if (!mInA.get(i) || !mInB.get(i)) {
						return false;
					}
				}
				return true;
			}
			if (!mInA.get(partition)) {
				return false;
			}
			if (mInB.get(partition)) {
				return true;
			}
			for (int i = partition - 1; i >= mStartOfSubtrees[partition];) {
				if (!mInB.get(i)) {
					return false;
				}
				i = mStartOfSubtrees[i] - 1;
			}
			return true;
		}

		public Occurrence intersect(final Occurrence other) {
			final BitSet inA = (BitSet) mInA.clone();
			final BitSet inB = (BitSet) mInB.clone();
			final BitSet containsMixedTerm = (BitSet) mContainsMixedTerm.clone();
			inA.and(other.mInA);
			inB.and(other.mInB);
			containsMixedTerm.and(other.mContainsMixedTerm);
			return new Occurrence(inA, inB, containsMixedTerm);
		}

		public boolean isAorShared(final int partition) {
			return mInA.get(partition);
		}

		public boolean isBorShared(final int partition) {
			return mInB.get(partition);
		}

		public boolean isALocal(final int partition) {
			return mInA.get(partition) && !mInB.get(partition);
		}

		public boolean isBLocal(final int partition) {
			return mInB.get(partition) && !mInA.get(partition);
		}

		public boolean isAB(final int partition) {
			return mInA.get(partition) && mInB.get(partition);
		}

		public boolean isMixed(final int partition) {
			return !mInA.get(partition) && !mInB.get(partition);
		}

		@Override
		public String toString() {
			return "[" + mInA + "|" + mInB + "]";
		}

		/**
		 * Find the first A-local colored node. Every occurrence has a A-local chain from such a node to the root node
		 * and all other nodes are not A-local.
		 *
		 * @return the first A-local colored node.
		 */
		public int getALocalColor() {
			int color = mInA.nextSetBit(0);
			if (mInB.get(color)) {
				color = mInB.nextClearBit(color);
			}
			return color;
		}
	}

	class LitInfo extends Occurrence {
		/**
		 * The mixed variable for mixed literals (in at least one partition).
		 */
		TermVariable mMixedVar;
		/**
		 * Tells for an equality whether the A part is the Lhs or the Rhs.
		 */
		Occurrence mLhsOccur;
		/**
		 * Gives for an inequality the A part.
		 */
		InterpolatorAffineTerm[] mAPart;

		public LitInfo() {
			super();
		}

		public LitInfo(final BitSet inA, final BitSet inB) {
			super(inA, inB);
		}

		public LitInfo(final BitSet inA, final BitSet inB, final BitSet containsMixedTerm) {
			super(inA, inB, containsMixedTerm);
		}

		public TermVariable getMixedVar() {
			return mMixedVar;
		}

		public Occurrence getLhsOccur() {
			return mLhsOccur;
		}

		public InterpolatorAffineTerm getAPart(final int p) {
			return mAPart[p];
		}
	}

	Term unfoldLAs(final Term interpolant) {
		final TermTransformer substitutor = new TermTransformer() {
			@Override
			public void convert(Term term) {
				if (LAInterpolator.isLATerm(term)) {
					term = ((AnnotatedTerm) term).getSubterm();
				}
				super.convert(term);
			}
		};
		return substitutor.transform(interpolant);
	}

	/**
	 * Color the input literals. This gets the source for the literals from the LeafNodes.
	 */
	private void colorLiterals(final Term proofTree) {

		final Set<Term> seen = new HashSet<>();
		final Deque<Term> todoStack = new ArrayDeque<>();
		seen.add(proofTree);
		todoStack.add(proofTree);

		while (!todoStack.isEmpty()) {
			final Term proofTerm = todoStack.pop();
			final InterpolatorClauseTermInfo proofTermInfo = getClauseTermInfo(proofTerm);
			if (proofTermInfo.isResolution()) {
				final Term primary = proofTermInfo.getPrimary();
				if (seen.add(primary)) {
					todoStack.add(primary);
				}
				final Term[] antecedents = proofTermInfo.getAntecedents();
				for (final Term a : antecedents) {
					assert a instanceof AnnotatedTerm;
					final Term subterm = ((AnnotatedTerm) a).getSubterm();
					if (seen.add(subterm)) {
						todoStack.add(subterm);
					}
				}
			} else {
				assert proofTermInfo.isLeaf();
				if (proofTermInfo.getLeafKind().equals(ProofConstants.FN_CLAUSE)) {
					// Color the literals
					final String source = proofTermInfo.getSource();
					final Term[] lits = proofTermInfo.getLiterals();
					final int partition = mPartitions.containsKey(source) ? mPartitions.get(source) : -1;

					for (int i = 0; i < lits.length; i++) {
						// Take the quoted literal!
						final Term atom = getAtom(lits[i]);
						LitInfo info = mAtomOccurenceInfos.get(atom);
						if (info == null) {
							info = new LitInfo();
							mAtomOccurenceInfos.put(atom, info);
						}
						if (!info.contains(partition)) {
							info.occursIn(partition);
							Term unquoted = atom;
							if (unquoted instanceof AnnotatedTerm) {
								unquoted = ((AnnotatedTerm) unquoted).getSubterm();
							}
							addOccurrence(unquoted, partition);
						}

						// Color all symbols occurring in the literal.
						colorSymbols(atom, partition);
					}
				}
			}
		}
	}

	Occurrence getOccurrence(final Term term) {
		if (term instanceof ConstantTerm) {
			return mFullOccurrence;
		}
		Occurrence result = mSymbolPartition.get(term);
		if (result == null) {
			if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getFunction().isIntern()) {
				final Term[] subTerms = ((ApplicationTerm) term).getParameters();
				result = mFullOccurrence;
				if (result.mContainsMixedTerm == null) {
					result.mContainsMixedTerm = new BitSet(mNumInterpolants + 1);
				}
				if (subTerms.length == 0) {
					return result;
				}
				for (final Term p : subTerms) {
					final Occurrence occ = getOccurrence(p);
					result = result.intersect(occ);
				}
			} else {
				// Compute occurrence of unknown term.
				result = getOccurrenceOfUnknownTerm(term);
			}
			mSymbolPartition.put(term, result);
		}
		return result;
	}

	void addOccurrence(final Term term, final int part) {
		if (term instanceof ConstantTerm) {
			/* Constant terms are always implicitly shared. */
			return;
		}
		Occurrence occ = mSymbolPartition.get(term);
		if (occ != null && occ.contains(part)) {
			/* Already colored correctly */
			return;
		}
		/* Recursively color subterms */
		if (term instanceof ApplicationTerm) {
			final ApplicationTerm at = (ApplicationTerm) term;
			for (final Term p : at.getParameters()) {
				addOccurrence(p, part);
			}
			if (at.getFunction().isIntern()) {
				return;
			}
		}
		/* Create occurrence if it is *not* an internal function and if it does not exists yet */
		if (occ == null) {
			occ = new Occurrence();
			mSymbolPartition.put(term, occ);
		}
		occ.occursIn(part);
	}

	// Compute the occurrence of a term seen for the first time.
	Occurrence getOccurrenceOfUnknownTerm(final Term term) {
		Occurrence result = mFullOccurrence;

		HashSet<String> symbols = getSymbols(term);
		for (String s : symbols) {
			if (!mSymbolOccurrenceInfos.containsKey(s)) {
				// If symbol is unknown, set symbol occurrence to root partition.
				mSymbolOccurrenceInfos.put(s, new Occurrence());
			}
			result = result.intersect(mSymbolOccurrenceInfos.get(s));
		}

		BitSet mixed = new BitSet(mPartitions.size());
		for (int part = 0; part < mPartitions.size(); part++) {
			// For a mixed term, set occurrence to the occurrence from the outermost
			// function symbol.
			if (result.isMixed(part)) {
				Occurrence purOcc = mSymbolOccurrenceInfos.get(((ApplicationTerm) term).getFunction().getName());
				if (purOcc.mInA.get(part)) {
					result.mInA.set(part);
				}
				if (purOcc.mInB.get(part)) {
					result.mInB.set(part);
				}
				mixed.set(part);
			}
		}
		result.mContainsMixedTerm = mixed;

		return result;
	}

	HashSet<Term> getSubTerms(final Term literal) {
		final HashSet<Term> subTerms = new HashSet<>();
		final ArrayDeque<Term> todo = new ArrayDeque<Term>();
		todo.addLast(literal);
		while (!todo.isEmpty()) {
			final Term term = todo.removeLast();
			if (subTerms.add(term)) {
				if (term instanceof ApplicationTerm) {
					final ApplicationTerm appTerm = (ApplicationTerm) term;
					for (final Term sub : appTerm.getParameters()) {
						todo.addLast(sub);
					}
				}
			}
		}
		return subTerms;
	}

	LitInfo getAtomOccurenceInfo(final Term atom) {
		assert !isNegatedTerm(atom);
		LitInfo result = mAtomOccurenceInfos.get(atom);
		if (result == null) {
			mLogger.info("colorLiteral: " + atom);
			result = colorMixedLiteral(atom);
		}
		return result;
	}

	/**
	 * Compute the LitInfo for a mixed Literal.
	 */
	public LitInfo colorMixedLiteral(final Term atom) {
		assert !isNegatedTerm(atom);
		assert !mAtomOccurenceInfos.containsKey(atom);

		final InterpolatorAtomInfo atomInfo = getAtomTermInfo(atom);

		final ArrayList<Term> subterms = new ArrayList<>();
		/*
		 * The sort of the auxiliary variable created for this atom. We need this since we internally represent integral
		 * constants in LIRA logics as Int even if they should have sort Real.
		 */
		Sort auxSort;
		if (atomInfo.isCCEquality()) {
			final ApplicationTerm eq = atomInfo.getEquality();
			final Term l = eq.getParameters()[0];
			final Term r = eq.getParameters()[1];
			subterms.add(l);
			subterms.add(r);
			assert l.getSort() == r.getSort();
			auxSort = l.getSort();
		} else {
			assert atomInfo.isLAEquality() || atomInfo.isBoundConstraint();
			subterms.addAll(atomInfo.getAffineTerm().getSummands().keySet());
			auxSort = atomInfo.isInt() ? mTheory.getNumericSort() : mTheory.getRealSort();
		}
		final LitInfo info = computeMixedOccurrence(subterms);
		mAtomOccurenceInfos.put(atom, info);

		final BitSet shared = new BitSet();
		shared.or(info.mInA);
		shared.or(info.mInB);
		if (shared.nextClearBit(0) >= mNumInterpolants) {
			return info;
		}

		info.mMixedVar = mTheory.createFreshTermVariable("litaux", auxSort);

		if (atomInfo.isCCEquality()) {
			final ApplicationTerm eq = atomInfo.getEquality();
			info.mLhsOccur = getOccurrence(eq.getParameters()[0]);
		} else if (atomInfo.isBoundConstraint() || atomInfo.isLAEquality()) {
			final InterpolatorAffineTerm lv = atomInfo.getAffineTerm();
			assert lv.getSummands().size() > 1 : "Mixed Literal with only one subterm: " + lv + " atom: " + atom;

			info.mAPart = new InterpolatorAffineTerm[mNumInterpolants];
			for (int part = 0; part < mNumInterpolants; part++) {
				if (!info.isMixed(part)) {
					continue;
				}

				final InterpolatorAffineTerm sumApart = new InterpolatorAffineTerm();
				for (final Entry<Term, Rational> en : lv.getSummands().entrySet()) {
					final Term var = en.getKey();
					final Occurrence occ = getOccurrence(var);
					if (occ.isALocal(part)) {
						final Rational coeff = en.getValue();
						sumApart.add(coeff, var);
					}
				}

				info.mAPart[part] = sumApart;
			}
		}
		return info;
	}

	private LitInfo computeMixedOccurrence(final ArrayList<Term> subterms) {
		LitInfo info;
		final BitSet inA = new BitSet(mNumInterpolants + 1);
		inA.set(0, mNumInterpolants + 1);
		final BitSet inB = new BitSet(mNumInterpolants + 1);
		inB.set(0, mNumInterpolants);
		for (final Term st : subterms) {
			final Occurrence occInfo = getOccurrence(st);
			inA.and(occInfo.mInA);
			inB.and(occInfo.mInB);
		}
		info = new LitInfo(inA, inB, containsMixedTerm);
		return info;
	}

	/**
	 * This term transformer substitutes an auxiliary variable by an arbitrary term. This is used for the LA and UF
	 * resolution rule. For the UF resolution rule, it will replace the auxiliary variable by the term that must be
	 * equal to it due to an EQ(x,s) term in the other interpolant. For the LA resolution rule, this will replace the
	 * auxiliary variable by -s1/c1 - i in F1/F2 (see paper). The replacement term may contain other auxiliary variables
	 * that will be replaced later. It may only contain auxiliary variables for equalities with the negated equality in
	 * the clause or auxiliary variables for LA literals that are bound by a surrounding LATerm.
	 *
	 * @author hoenicke
	 */
	public static class Substitutor extends TermTransformer {
		TermVariable mTermVar;
		Term mReplacement;

		public Substitutor(final TermVariable termVar, final Term replacement) {
			mTermVar = termVar;
			mReplacement = replacement;
		}

		private static boolean isSMTAffineTerm(Term term) {
			if (!term.getSort().isNumericSort()) {
				return false;
			}
			if (term instanceof ApplicationTerm) {
				FunctionSymbol fsym = ((ApplicationTerm) term).getFunction();
				return fsym.isIntern() && (fsym.getName() == "+" || fsym.getName() == "-" || fsym.getName() == "*"
						|| fsym.getName() == "to_real");
			} else if (term instanceof ConstantTerm) {
				return true;
			}
			return false;
		}

		@Override
		public void convert(final Term oldTerm) {
			if (isSMTAffineTerm(oldTerm)) {
				final SMTAffineTerm oldAffine = new SMTAffineTerm(oldTerm);
				final Term[] oldSummands =
						oldAffine.getSummands().keySet().toArray(new Term[oldAffine.getSummands().size()]);
				/* recurse into LA term */
				enqueueWalker(new Walker() {
					@Override
					public void walk(final NonRecursive engine) {
						final Substitutor me = (Substitutor) engine;
						final Term[] newSummands = me.getConverted(oldSummands);
						// did we change something?
						if (newSummands == oldSummands) {
							me.setResult(oldTerm);
							return;
						}
						// create new SMTAffineTerm from newSummands and old coefficients
						final SMTAffineTerm newAffine = new SMTAffineTerm();
						for (int i = 0; i < oldSummands.length; i++) {
							newAffine.add(oldAffine.getSummands().get(oldSummands[i]), newSummands[i]);
						}
						newAffine.add(oldAffine.getConstant());
						// create the new LA term
						me.setResult(newAffine.toTerm(oldTerm.getSort()));
					}
				});
				pushTerms(oldSummands);
				return;
			} else if (LAInterpolator.isLATerm(oldTerm)) {
				final InterpolatorAffineTerm oldS = LAInterpolator.getS(oldTerm);
				final InfinitesimalNumber oldK = LAInterpolator.getK(oldTerm);
				final Term oldF = LAInterpolator.getF(oldTerm);
				final Term[] oldSummands =
						oldS.getSummands().keySet().toArray(new Term[oldS.getSummands().size()]);
				/* recurse into LA term */
				enqueueWalker(new Walker() {
					@Override
					public void walk(final NonRecursive engine) {
						final Substitutor me = (Substitutor) engine;
						final Term newF = me.getConverted();
						final Term[] newSummands = me.getConverted(oldSummands);
						// did we change something?
						if (newF == oldF && newSummands == oldSummands) {
							me.setResult(oldTerm);
							return;
						}
						// create newS term from newSummands and old coefficients
						final InterpolatorAffineTerm newS = new InterpolatorAffineTerm();
						for (int i = 0; i < oldSummands.length; i++) {
							newS.add(oldS.getSummands().get(oldSummands[i]), newSummands[i]);
						}
						newS.add(oldS.getConstant());
						// create the new LA term
						me.setResult(LAInterpolator.createLATerm(newS, oldK, newF));
					}
				});
				pushTerm(oldF);
				pushTerms(oldSummands);
				return;
			} else if (oldTerm.equals(mTermVar)) {
				setResult(mReplacement);
			} else {
				super.convert(oldTerm);
			}
		}
	}

	/**
	 * Substitute termVar by replacement in mainTerm. This will also work correctly with LATerms.
	 *
	 * @param mainTerm
	 *            the term where the replacement is done.
	 * @param termVar
	 *            the variable to replace.
	 * @param replacement
	 *            the replacement term.
	 * @return the substituted term.
	 */
	Term substitute(final Term mainTerm, final TermVariable termVar, final Term replacement) {
		return new Substitutor(termVar, replacement).transform(mainTerm);
	}

	class EQSubstitutor extends TermTransformer {
		Term mI2;
		TermVariable mAuxVar;

		EQSubstitutor(final Term i2, final TermVariable auxVar) {
			mI2 = i2;
			mAuxVar = auxVar;
		}

		@Override
		public void convert(final Term term) {
			assert term != mAuxVar;
			if (term instanceof ApplicationTerm) {
				final ApplicationTerm appTerm = (ApplicationTerm) term;
				final FunctionSymbol func = appTerm.getFunction();
				final Term[] params = appTerm.getParameters();
				if (func.isIntern() && func.getName().equals(EQ) && params[0] == mAuxVar) {
					assert params.length == 2;
					setResult(substitute(mI2, mAuxVar, params[1]));
					return;
				}
			}
			super.convert(term);
		}
	}

	/**
	 * Compute the interpolant for the resolution rule with a mixed equality as pivot. This is I1[I2(s_i)] for
	 * I1[EQ(x,s_i)] and I2(x).
	 *
	 * @param eqIpol
	 *            the interpolant I1[EQ(x,s_i)].
	 * @param neqIpol
	 *            the interpolant I2(x).
	 * @param mixedVar
	 *            the auxiliary variable x.
	 * @return the resulting interpolant.
	 */
	private Term mixedEqInterpolate(final Term eqIpol, final Term neqIpol,
			final TermVariable mixedVar) {
		final TermTransformer ipolator = new EQSubstitutor(neqIpol, mixedVar);
		return ipolator.transform(eqIpol);
	}

	static abstract class MixedLAInterpolator extends TermTransformer {
		TermVariable mMixedVar;
		Term mI2;
		AnnotatedTerm mLA1;

		public MixedLAInterpolator(final Term i2, final TermVariable mixed) {
			mMixedVar = mixed;
			mLA1 = null;
			mI2 = i2;
		}

		abstract Term interpolate(AnnotatedTerm la1, AnnotatedTerm la2);

		@Override
		public void convert(final Term term) {
			assert term != mMixedVar;
			if (LAInterpolator.isLATerm(term)) {
				final AnnotatedTerm laTerm = (AnnotatedTerm) term;
				final InterpolatorAffineTerm s2 = LAInterpolator.getS(term);
				if (s2.getSummands().get(mMixedVar) != null) { // NOPMD
					if (mLA1 == null) {
						/*
						 * We are inside I1. Remember the lainfo and push I2 on the convert stack. Also enqueue a walker
						 * that will remove m_LA1 once we are finished with I2.
						 */
						beginScope();
						mLA1 = laTerm;
						enqueueWalker(new Walker() {
							@Override
							public void walk(final NonRecursive engine) {
								((MixedLAInterpolator) engine).mLA1 = null;
								((MixedLAInterpolator) engine).endScope();
							}
						});
						pushTerm(mI2);
						return;
					} else {
						/*
						 * We are inside I2. Interpolate the LAInfos.
						 */
						setResult(interpolate(mLA1, laTerm));
						return;
					}
				}
			}
			super.convert(term);
		}
	}

	class RealInterpolator extends MixedLAInterpolator {
		public RealInterpolator(final Term i2, final TermVariable mixedVar) {
			super(i2, mixedVar);
		}

		@Override
		public Term interpolate(final AnnotatedTerm la1, final AnnotatedTerm la2) {
			// retrieve c1,c2,s2,s2
			final InterpolatorAffineTerm s1 = LAInterpolator.getS(la1);
			final Rational c1 = s1.getSummands().get(mMixedVar);
			final InfinitesimalNumber k1 = LAInterpolator.getK(la1);
			final InterpolatorAffineTerm s2 = LAInterpolator.getS(la2);
			final Rational c2 = s2.getSummands().get(mMixedVar);
			final InfinitesimalNumber k2 = LAInterpolator.getK(la2);
			assert c1.signum() * c2.signum() == -1;
			InfinitesimalNumber newK = k1.mul(c2.abs()).add(k2.mul(c1.abs()));

			// compute c1s2 + c2s1
			final InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
			c1s2c2s1.add(c1.abs(), s2);
			c1s2c2s1.add(c2.abs(), s1);
			assert !c1s2c2s1.getSummands().containsKey(mMixedVar);

			Term newF;
			if (s1.getConstant().mEps > 0 || s2.getConstant().mEps > 0) {
				// One of the inequalities is strict. In this case
				// c1s2c2s1 must also be a strict inequality and it is not
				// possible that c1s2c2s1 == 0 holds. Hence, we do not need
				// to substitute a shared term.
				newF = c1s2c2s1.toLeq0(mTheory);
				newK = InfinitesimalNumber.EPSILON.negate();
			} else if (k1.less(InfinitesimalNumber.ZERO)) {
				// compute -s1/c1
				final InterpolatorAffineTerm s1divc1 = new InterpolatorAffineTerm(s1);
				s1divc1.getSummands().remove(mMixedVar);
				s1divc1.mul(c1.inverse().negate());
				final Term s1DivByc1 = s1divc1.toSMTLib(mTheory, false);
				newF = substitute(la2.getSubterm(), mMixedVar, s1DivByc1);
				newK = k2;
			} else if (k2.less(InfinitesimalNumber.ZERO)) {
				// compute s2/c2
				final InterpolatorAffineTerm s2divc2 = new InterpolatorAffineTerm(s2);
				s2divc2.getSummands().remove(mMixedVar);
				s2divc2.mul(c2.inverse().negate());
				final Term s2DivByc2 = s2divc2.toSMTLib(mTheory, false);
				newF = substitute(la1.getSubterm(), mMixedVar, s2DivByc2);
				newK = k1;
			} else {
				final InterpolatorAffineTerm s1divc1 = new InterpolatorAffineTerm(s1);
				s1divc1.getSummands().remove(mMixedVar);
				s1divc1.mul(c1.inverse().negate());
				final Term s1DivByc1 = s1divc1.toSMTLib(mTheory, false);
				final Term f1 = substitute(la1.getSubterm(), mMixedVar, s1DivByc1);
				final Term f2 = substitute(la2.getSubterm(), mMixedVar, s1DivByc1);
				newF = mTheory.and(f1, f2);
				if (c1s2c2s1.isConstant()) {
					if (c1s2c2s1.getConstant().less(InfinitesimalNumber.ZERO)) {
						newF = mTheory.mTrue;
					}
				} else {
					final InterpolatorAffineTerm s3 = new InterpolatorAffineTerm(c1s2c2s1);
					s3.add(InfinitesimalNumber.EPSILON);
					newF = mTheory.or(s3.toLeq0(mTheory), newF);
				}
				newK = InfinitesimalNumber.ZERO;
			}
			return LAInterpolator.createLATerm(c1s2c2s1, newK, newF);
		}
	}

	class IntegerInterpolator extends MixedLAInterpolator {

		public IntegerInterpolator(final Term i2, final TermVariable mixedVar) {
			super(i2, mixedVar);
		}

		@Override
		public Term interpolate(final AnnotatedTerm la1, final AnnotatedTerm la2) {
			// retrieve c1,c2,s1,s2
			final InterpolatorAffineTerm s1 = LAInterpolator.getS(la1);
			final Rational c1 = s1.getSummands().get(mMixedVar);
			final InfinitesimalNumber k1 = LAInterpolator.getK(la1);
			final InterpolatorAffineTerm s2 = LAInterpolator.getS(la2);
			final Rational c2 = s2.getSummands().get(mMixedVar);
			final InfinitesimalNumber k2 = LAInterpolator.getK(la2);
			assert c1.isIntegral() && c2.isIntegral();
			assert c1.signum() * c2.signum() == -1;
			final Rational absc1 = c1.abs();
			final Rational absc2 = c2.abs();

			// compute c1s2 + c2s1
			final InterpolatorAffineTerm c1s2c2s1 = new InterpolatorAffineTerm();
			c1s2c2s1.add(absc1, s2);
			c1s2c2s1.add(absc2, s1);
			assert !c1s2c2s1.getSummands().containsKey(mMixedVar);

			// compute newk = c2k1 + c1k2 + c1c2;
			final Rational c1c2 = absc1.mul(absc2);
			final InfinitesimalNumber newK = k1.mul(absc2).add(k2.mul(absc1)).add(new InfinitesimalNumber(c1c2, 0));
			assert newK.isIntegral();

			final Rational k1c1 = k1.mReal.add(Rational.ONE).div(absc1).ceil();
			final Rational k2c2 = k2.mReal.add(Rational.ONE).div(absc2).ceil();
			Rational kc;
			Rational theC;
			InterpolatorAffineTerm theS;
			if (k1c1.compareTo(k2c2) < 0) {
				theC = c1;
				theS = s1;
				kc = k1c1;
			} else {
				theC = c2;
				theS = s2;
				kc = k2c2;
			}
			Term newF = mTheory.mFalse;
			// Use -s/c as start value.
			final InterpolatorAffineTerm sPlusOffset = new InterpolatorAffineTerm();
			sPlusOffset.add(theC.signum() > 0 ? Rational.MONE : Rational.ONE, theS);
			sPlusOffset.getSummands().remove(mMixedVar);
			Rational offset = Rational.ZERO;
			final Rational theCabs = theC.abs();
			if (theC.signum() < 0) {
				sPlusOffset.add(theCabs.add(Rational.MONE));
			}
			while (offset.compareTo(kc) <= 0) {
				Term x;
				if (mCancel.isTerminationRequested()) {
					throw new SMTLIBException("Timeout exceeded");
				}
				x = sPlusOffset.toSMTLib(mTheory, true);
				if (theCabs != Rational.ONE) {
					x = mTheory.term("div", x, theCabs.toTerm(mTheory.getNumericSort()));
				}
				Term F1 = substitute(la1.getSubterm(), mMixedVar, x);
				Term F2 = substitute(la2.getSubterm(), mMixedVar, x);

				if (offset.compareTo(kc) == 0) {
					if (theS == s1) {
						F1 = mTheory.mTrue;
					} else {
						F2 = mTheory.mTrue;
					}
				}
				newF = mTheory.or(newF, mTheory.and(F1, F2));
				sPlusOffset.add(theC.negate());
				offset = offset.add(Rational.ONE);
			}
			return LAInterpolator.createLATerm(c1s2c2s1, newK, newF);
		}

	}

	/**
	 * Compute the interpolant for the resolution rule with a mixed inequality as pivot. This is I1[I2(LA3)] for I1[LA1]
	 * and I2[LA2]. Note that we use only one auxiliary variable, which corresponds to x_1 and -x_2 in the paper.
	 *
	 * @param leqItp
	 *            the interpolant I1[LA1].
	 * @param sgItp
	 *            the interpolant I2[LA2].
	 * @param mixedVar
	 *            the auxiliary variable x used in the la term.
	 * @return the resulting interpolant.
	 */
	public Term mixedPivotLA(final Term leqItp, final Term sgItp, final TermVariable mixedVar) {
		final MixedLAInterpolator ipolator;

		if (mixedVar.getSort().getName().equals("Real")) {
			ipolator = new RealInterpolator(sgItp, mixedVar);
		} else {
			ipolator = new IntegerInterpolator(sgItp, mixedVar);
		}
		final Term newI = ipolator.transform(leqItp);
		return newI;
	}

	/**
	 * Get all the information the interpolator needs for this term. Known InterpolatorTermInfos are stored in a HashMap
	 * to avoid recalculating them. This can be used for complex proof terms such as complete resolution steps or
	 * lemmata, but also for single literals.
	 */
	InterpolatorClauseTermInfo getClauseTermInfo(final Term term) {
		if (mClauseTermInfos.containsKey(term)) {
			return mClauseTermInfos.get(term);
		}
		final InterpolatorClauseTermInfo info = new InterpolatorClauseTermInfo(term);
		mClauseTermInfos.put(term, info);
		return info;
	}

	InterpolatorAtomInfo getAtomTermInfo(final Term term) {
		assert !isNegatedTerm(term);
		if (mLiteralTermInfos.containsKey(term)) {
			return mLiteralTermInfos.get(term);
		}
		final InterpolatorAtomInfo info = new InterpolatorAtomInfo(term);
		mLiteralTermInfos.put(term, info);
		return info;
	}

	/**
	 * Get the unquoted literal. The main problem here is that the quote annotation is inside the negation for negated
	 * literals.
	 *
	 * @param literal
	 * @return the literal without the quoted annotation
	 */
	Term unquote(final Term literal) {
		final Term atom = getAtom(literal);
		Term unquoted = atom;
		if (unquoted instanceof AnnotatedTerm) {
			assert ((AnnotatedTerm) unquoted).getAnnotations()[0].getKey().startsWith(":quoted");
			unquoted = ((AnnotatedTerm) unquoted).getSubterm();
		}
		if (atom != literal) {
			unquoted = mTheory.term("not", unquoted);
		}
		return unquoted;
	}

	/**
	 * Collect all non-logical symbols in a term.
	 */
	public HashSet<String> getSymbols(final Term term) {
		assert term != null;

		final HashSet<String> result = new HashSet<String>();
		final Deque<Term> todoStack = new ArrayDeque<>();

		todoStack.add(unquote(term));

		while (!todoStack.isEmpty()) {
			Term t = todoStack.pop();
			if (t instanceof TermVariable || t instanceof ConstantTerm) {
				continue;
			}
			if (t instanceof QuantifiedFormula) {
				t = unquote(((QuantifiedFormula) t).getSubformula());
			}
			if (t instanceof AnnotatedTerm) {
				t = ((AnnotatedTerm) t).getSubterm();
			}
			ApplicationTerm at = (ApplicationTerm) t;

			FunctionSymbol funSymbol = at.getFunction();
			String symbol = funSymbol.getName();
			Term[] params = at.getParameters();

			for (int i = 0; i < params.length; i++) {
				todoStack.add(params[i]);
			}
			// Add symbol if it is not an internal symbol
			if (!funSymbol.isIntern()) {
				result.add(symbol);
			}
		}
		return result;
	}

	/**
	 * Return the depth of nested functions for a term with given depth.
	 */
	int getNestingDepth(final ApplicationTerm term, int n) {
		if (term.getParameters().length == 0) {
			return n;
		} else {
			int nMax = n;
			for (int i = 0; i < term.getParameters().length; i++) {
				int j = getNestingDepth((ApplicationTerm) term.getParameters()[i], n + 1);
				nMax = (j > nMax) ? j : nMax;
			}
			return nMax;
		}
	}

	/**
	 * Return a list of terms with descending number of nested function depth.
	 */
	ArrayList<Term> orderTerms(final HashSet<Term> terms) {
		final ArrayList<Term> ordered = new ArrayList<Term>();
		final HashMap<Term, Integer> info = new HashMap<Term, Integer>();

		// Collect nested function depth for all terms.
		for (Term t : terms) {
			ApplicationTerm at = (ApplicationTerm) t;

			if (info.get(at) == null) {
				info.put(at, getNestingDepth(at, 0));
			}
		}
		// Order terms in descending order of nested function depth.
		for (Term t : terms) {
			ApplicationTerm at = (ApplicationTerm) t;
			int n = 0;
			for (int i = 0; i < ordered.size(); i++) {
				if (info.get(at) > info.get(ordered.get(i))) {
					n = i;
					break;
				}
			}
			ordered.add(n, at);
		}
		return ordered;
	}

	/**
	 * Update the color of all non-logical symbols in a given term according to the
	 * given partition.
	 */
	public void colorSymbols(final Term literal, final int partition) {
		assert literal != null;

		HashSet<String> symbols = getSymbols(literal);
		for (String symbol : symbols) {
			Occurrence funOcc = new Occurrence();
			if (mSymbolOccurrenceInfos.containsKey(symbol)) {
				funOcc = mSymbolOccurrenceInfos.get(symbol);
			}
			funOcc.occursIn(partition);
			mSymbolOccurrenceInfos.put(symbol, funOcc);
		}
	}

	/**
	 * Replace all non-shared symbols in the interpolants by auxiliary variables.
	 * 
	 * @param interpolants Array of interpolants that possibly contain non-shared
	 *                     symbols.
	 * @return resulting Array of interpolants only containing shared symbols.
	 */
	private Term[] replaceNonsharedSymbols(Term[] interpolants) {
		// Term interpolant = null;

		for (int i = 0; i < interpolants.length; i++) {
			Term interpolant = interpolants[i];
			HashSet<String> nonSharedSymbols = getNonsharedSymbols(interpolant, i);

			if (nonSharedSymbols.isEmpty()) {
				// The current interpolant only contains shared symbols.
				continue;
			}
			HashSet<Term> subTerms = getAllSubTerms(interpolant);

			// Collect the subterms that need to be replaced.
			for (String s : nonSharedSymbols) {
				HashSet<Term> replace = new HashSet<Term>(subTerms);
				for (Term sub : subTerms) {
					if (sub instanceof TermVariable || ((ApplicationTerm) sub).getFunction().getName() != s) {
						replace.remove(sub);
					}
				}

				// Order in which we replace subterms in nested functions may effect result,
				// i.e. if we have f(f(a)) and we want to replace f(...), we should start with
				// the outermost occurrence of f.
				ArrayList<Term> ordered = orderTerms(replace);

				// Replace the term by a variable
				for (int j = 0; j < ordered.size(); j++) {
					TermVariable auxVar;
					Term t = ordered.get(j);
					Sort sort = t.getSort();
					// Is there already a mapping from term to variable?
					if (mMixedTermAuxEq.containsKey(t)) {
						auxVar = mMixedTermAuxEq.get(t);
					} else {
						// Create fresh variable.
						auxVar = mTheory.createFreshTermVariable("purAux", sort);
						mMixedTermAuxEq.put(t, auxVar);
					}
					final TermTransformer ipolator = new TermSubstitutor(t, auxVar);
					interpolants[i] = ipolator.transform(interpolants[i]);
				}
			}
		}
		return interpolants;
	}

	/**
	 * Collect all non-logical symbols in a given term that are not AB-shared in the
	 * given partition.
	 */
	public HashSet<String> getNonsharedSymbols(final Term term, final int partition) {
		HashSet<String> result = new HashSet<String>();
		HashSet<String> symbols = getSymbols(term);

		for (String s : symbols) {
			assert mSymbolOccurrenceInfos.get(s) != null;
			if (!mSymbolOccurrenceInfos.get(s).isAB(partition)) {
				result.add(s);
			}
		}
		return result;
	}

	/**
	 * Collect the set of unsupported variables relative to a given clause from a
	 * list of variables .
	 * 
	 * @param variables The variables to be checked
	 * @param clause    The clause against which the variables are checked
	 * @return Set of TermVariables that are not supported by the clause
	 */
	private HashSet<TermVariable> getUnsupportedVariables(ArrayList<TermVariable> variables, Term[] clause) {
		HashSet<TermVariable> result = new HashSet<TermVariable>();
		HashSet<Term> subTerms = new HashSet<Term>();

		if (variables.isEmpty()) {
			return result;
		}

		for (int i = 0; i < clause.length; i++) {
			subTerms.addAll(getAllSubTerms(clause[i]));
		}

		// Check if term that was replaced by the variable is a subterm of the clause.
		for (int i = 0; i < variables.size(); i++) {
			Term replaced = null;
			for (Entry<Term, TermVariable> e : mMixedTermAuxEq.entrySet()) {
				if (e.getValue().equals(variables.get(i))) {
					replaced = (Term) e.getKey();
					break;
				}
			}
			// If term is not contained in the subterms, the corresponding variable is
			// unsupported.
			if (!subTerms.contains(replaced)) {
				result.add(variables.get(i));
			}
		}
		return result;
	}

	/**
	 * For a given set of variables and their mapping to the terms they replace,
	 * return a list where the given variables are ordered according to their
	 * dependencies, i.e. For v1, v2 with dependency v1=f(v2), we return [v2,v1].
	 * Only works if variable dependencies do not contain cycles.
	 * 
	 * @param unsupported    Set of variables to be sorted.
	 * @param variableToTerm Set containing mapping between variables and the terms
	 *                       that they replaced.
	 * @return List of variables in dependency order.
	 */
	private List<TermVariable> sortVariables(HashMap<TermVariable, Term> map) {
		HashMap<TermVariable, HashSet<TermVariable>> dependencies = new HashMap<TermVariable, HashSet<TermVariable>>();

		// Build dependency map.
		for (Entry<TermVariable, Term> e1 : map.entrySet()) {
			Term t1 = (Term) e1.getValue();
			HashSet<TermVariable> deps = new HashSet<TermVariable>();
			for (Entry<TermVariable, Term> e2 : map.entrySet()) {
				if (e1.equals(e2)) {
					continue;
				}
				Term t2 = (Term) e2.getValue();
				// check if v2 is subTerm of v1
				HashSet<Term> sub = getAllSubTerms(t1);
				if (sub.contains(t2)) {
					deps.add((TermVariable) e2.getKey());
				}
			}
			dependencies.put((TermVariable) e1.getKey(), deps);
		}

		Deque<TermVariable> todoStack = new ArrayDeque<TermVariable>(map.keySet());
		List<TermVariable> ordered = new ArrayList<TermVariable>();
		TermVariable seen = null;
		Boolean reset = true;

		// Compute dependency ordered list.
		while (!todoStack.isEmpty()) {
			TermVariable tv = todoStack.pop();
			if (tv == seen) {
				throw new IllegalArgumentException("Variable dependencies must not contain cycles.");
			}
			// Only add a variable to the ordered list if all variables on which it depends
			// are already present.
			if (dependencies.get(tv).isEmpty() || ordered.containsAll(dependencies.get(tv))) {
				ordered.add(tv);
				reset = true;
				seen = tv;
			} else {
				todoStack.add(tv);
				if (reset) {
					seen = tv;
					reset = false;
				}
			}
		}
		return ordered;
	}

	/**
	 * Add quantifiers to the provisional interpolants for a given clause if the
	 * provisional interpolant contains auxiliary variables that are not supported
	 * by the clause.
	 * 
	 * @param interpolants Set of provisional interpolants for the clause
	 * @param clause       The clause for which the interpolants should be computed
	 * @return The modified interpolant.
	 */
	private Term[] addQuantifier(final Term[] interpolants, Term[] clause) {
		ArrayList<TermVariable> vars = new ArrayList<TermVariable>();
		HashMap<TermVariable, Term> termToAuxEq = (HashMap<TermVariable, Term>) mMixedTermAuxEq.entrySet().stream()
				.collect(Collectors.toMap(Map.Entry::getValue, Map.Entry::getKey));
		HashMap<TermVariable, Term> mapUnsupported = new HashMap<TermVariable, Term>();

		if (termToAuxEq.isEmpty()) {
			return interpolants;
		}
		// Get the list of mixed-term auxiliary variables introduced for the clause.
		vars.addAll((Collection<? extends TermVariable>) termToAuxEq.keySet());

		// Collect those auxiliary variables not supported by the clause.
		HashSet<TermVariable> unsupported = getUnsupportedVariables(vars, clause);
		if (unsupported.isEmpty()) {
			return interpolants;
		}

		// Store mapping from variable to term for unsupported variables.
		for (TermVariable tv : unsupported) {
			mapUnsupported.put(tv, termToAuxEq.get(tv));
		}

		// Sort unsupported variables in dependency order.
		List<TermVariable> ordered = sortVariables(mapUnsupported);

		// Insert quantifiers for unsupported variables in inverse dependency order.
		for (int i = 0; i < mNumInterpolants; i++) {
			for (int j = ordered.size() - 1; j >= 0; j--) {
				if (!getTermVariables(interpolants[i]).contains(ordered.get(j))) {
					continue;
				}
				// Get term that was replaced by the variable
				String outermost = ((ApplicationTerm) mapUnsupported.get(ordered.get(j))).getFunction().getName();

				// Add quantifier according to color of outermost function symbol.
				if (mSymbolOccurrenceInfos.get(outermost).isALocal(i)) {
					interpolants[i] = mTheory.exists(new TermVariable[] { ordered.get(j) }, interpolants[i]);
				} else {
					interpolants[i] = mTheory.forall(new TermVariable[] { ordered.get(j) }, interpolants[i]);
				}
			}
		}
		return interpolants;
	}

	public boolean isNegatedTerm(final Term literal) {
		return literal instanceof ApplicationTerm && ((ApplicationTerm) literal).getFunction().getName().equals("not");
	}

	public Term getAtom(final Term literal) {
		return isNegatedTerm(literal) ? ((ApplicationTerm) literal).getParameters()[0] : literal;
	}
}
