import java.util.List;

public class Case24 {
	/**
	 * parameter: integer whose k-th bit is the result of the block function applied
	 * to a tuple that is the little-endian binary representation of k
	 * 
	 * rank: rank of the function f
	 * 
	 * mask: allows selecting only the rank relevant bits of n when computing the
	 * term u_n
	 * 
	 * SHIFTS: integers whose non-zero binary digits are at positions 1, 2, 4, 8 and
	 * 16
	 */
	private static long parameter;
	private static int rank;
	private static int mask;
	private static final List<Integer> SHIFTS = List.of(0, 2, 4, 6, 16, 18, 20, 22, 256, 258, 260, 262, 272, 274, 276,
			278, 65536, 65538, 65540, 65542, 65552, 65554, 65556, 65558, 65792, 65794, 65796, 65798, 65808, 65810, 65812,
			65814);

	/**
	 * Applies the block function to a tuple of binary digits
	 */
	private static int f(int a, int b, int c, int d, int e) {
		return (parameter & (1 << (a + 2 * b + 4 * c + 8 * d + 16 * e))) == 0 ? 0 : 1;
	}

	/**
	 * Checks whether the block function is (rank-2,rank)-strongly 2-uncorrelated.
	 * We go over all possible bitmasks, eq, between related vectors
	 */
	private static boolean goodFamily() {
		for (int len = 0; len < rank; len++) {
			for (int i = 0; i < (1 << len); i++) {
				boolean[] eq = new boolean[len + rank];
				int[] xBuffer = new int[len + rank];
				int[] yBuffer = new int[len + rank];
				for (int j = 0; j < len; j++) {
					eq[j] = ((i >> j) & 1) != 0;
				}
				for (int j = len; j < len + rank; j++) {
					eq[j] = true;
				}
				yBuffer[len] = 1;
				if (!family(eq, xBuffer, yBuffer, 0)) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Investigates a subset of the families F(x,y)
	 * 
	 * @param eq:      bitmask indicating at which positions x and y must coincide
	 * @param offset:  positions at which x and y already have fixed values
	 * @param xBuffer: vector x
	 * @param yBuffer: vector y
	 */
	private static boolean family(boolean[] eq, int[] xBuffer, int[] yBuffer, int offset) {
		if (offset == eq.length) {
			int[] tab = new int[2];
			fill(eq, xBuffer, yBuffer, 0, tab);
			return tab[0] == tab[1];
		}
		if (eq[offset]) {
			return family(eq, xBuffer, yBuffer, offset + 1);
		}
		xBuffer[offset] = 0;
		yBuffer[offset] = 1;
		if (!family(eq, xBuffer, yBuffer, offset + 1)) {
			return false;
		}
		xBuffer[offset] = 1;
		yBuffer[offset] = 0;
		if (!family(eq, xBuffer, yBuffer, offset + 1)) {
			return false;
		}
		return true;
	}

	/**
	 * Investigates a given family F(x,y)
	 * 
	 * @param eq:      bitmask indicating at which positions x and y must coincide
	 * @param offset:  positions at which x and y already have fixed values
	 * @param xBuffer: vector x
	 * @param yBuffer: vector y
	 * @param tab:     counts how many 0s and 1s were already seen
	 */
	private static void fill(boolean[] eq, int[] xBuffer, int[] yBuffer, int offset, int[] tab) {
		if (offset == eq.length) {
			tab[(value(xBuffer) + value(yBuffer)) & 1]++;
		} else if (offset != eq.length - rank && eq[offset]) {
			xBuffer[offset] = 0;
			yBuffer[offset] = 0;
			fill(eq, xBuffer, yBuffer, offset + 1, tab);
			xBuffer[offset] = 1;
			yBuffer[offset] = 1;
			fill(eq, xBuffer, yBuffer, offset + 1, tab);
		} else {
			fill(eq, xBuffer, yBuffer, offset + 1, tab);
		}
	}

	/**
	 * Computes f(x)
	 */
	private static int value(int[] xBuffer) {
		int sum = 0;
		for (int i = 0; i + rank <= xBuffer.length; i++) {
			sum += f(xBuffer[i], xBuffer[i + 1], rank > 2 ? xBuffer[i + 2] : 0, rank > 3 ? xBuffer[i + 3] : 0,
					rank > 4 ? xBuffer[i + 4] : 0);
		}
		return sum;
	}

	/**
	 * Computes u_n
	 */
	private static int eval(int n) {
		int result = 0;
		while (n > 0) {
			if ((parameter & (1 << (n & mask))) != 0) {
				result++;
			}
			n >>= 1;
		}
		return result & 1;
	}

	/**
	 * Runs the loop of Algorithm 1 in case delta = (0,a) and m = log(classes.length)
	 */
	private static boolean has2Correlation(int a, int[] classes) {
		int[] tab = new int[2];
		int small = classes.length >> 3;
		for (int n = 0; n + a < classes.length; n++) {
			if (small > 0 && n / small == (n + a) / small) {
				tab[(classes[n] + classes[n + a]) & 1]++;
			}
		}
		return Math.max(tab[0], tab[1]) > (classes.length >> 1);
	}

	/**
	 * Looks for a witness that (u_n) is 2-correlated, by checking all parameters m
	 * < Nmax and all vectors delta = (0,a) with Kmin <= a < Kmax
	 */
	private static boolean has2Correlation(int Nmax, int Kmin, int Kmax) {
		for (int m = 2; m < Nmax; m++) {
			int M = 1 << m;
			int[] classes = new int[M];
			for (int i = 0; i < M; i++) {
				classes[i] = eval(i);
			}
			for (int a = Kmin; a < Kmax; a++) {
				if (has2Correlation(a, classes)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Runs the loop of Algorithm 1 in case delta = (0,a,b,c) and m = log(classes.length)
	 */
	private static boolean has4Correlation(int a, int b, int c, int[] classes) {
		int[][][] tab = new int[2][2][2];
		int small = classes.length >> 4;
		for (int n = 0; n + c < classes.length; n++) {
			if (n / small == (n + b) / small) {
				tab[(classes[n] + classes[n + a]) & 1][(classes[n] + classes[n + b]) & 1][(classes[n] + classes[n + c]) & 1]++;
			}
		}
		for (int i = 0; i < 2; i++) {
			for (int j = 0; j < 2; j++) {
				for (int k = 0; k < 2; k++) {
					if (tab[i][j][k] > classes.length / 8) {
						return true;
					}
				}
			}
		}
		return false;
	}

	/**
	 * Looks for a witness that (u_n) is 4-correlated, by checking all parameters m
	 * <= 2^(Nmax-1) and all vectors delta = (0,a,b,c) with d < K
	 */
	private static boolean has4Correlation(int max, int K) {
		for (int n = 6; n <= max; n++) {
			int N = 1 << n;
			int[] classes = new int[N];
			for (int i = 0; i < N; i++) {
				classes[i] = eval(i);
			}
			for (int c = 3; c < K; c++) {
				for (int b = 2; b < c; b++) {
					for (int a = 1; a < b; a++) {
						if (has4Correlation(a, b, c, classes)) {
							return true;
						}
					}
				}
			}
		}
		return false;
	}

	/**
	 * Transforms a (2^rank - rank - 1)-bit-long integer into a 2^rank-bit-long one,
	 * whose bits at positions 0 or a power of 2 are 0s. This allows selecting only
	 * block functions f such that f(0,0,...,0) = 0 and taking exactly one
	 * representative up to adding selection-projection functions.
	 */
	private static long getParameter(long p) {
		return ((p & 1) << 3) | ((p & 14) << 4) | ((p & 2032) << 5) | ((p & 67106816) << 6);
	}

	/**
	 * Checks that each sequence with rank r is either 2-correlated or
	 * (r-2,r)-strongly 2-uncorrelated, counts those that are 2-uncorrelated, and
	 * checks that they are 4-correlated.
	 */
	private static long countGoodFunctions(int r) {
		long good = 0;
		rank = r;
		mask = (1 << rank) - 1;
		long max = 1L << (mask - rank);
		for (long p = 0; p < max; p++) {
			parameter = getParameter(p);
			if (goodFamily()) {
				good++;
				for (int i : SHIFTS) {
					if (i < (1 << mask)) {
						parameter ^= i;
						if (!has4Correlation(10, 7)) {
							throw new RuntimeException("Classification problem: 4-uncorrelated function!");
						}
						parameter ^= i;
					}
				}
			} else if (!has2Correlation(15, 1, 8) && !has2Correlation(15, 8, 18)) {
				throw new RuntimeException("Classification problem!");
			}
		}
		return good << r;
	}

	/**
	 * Checks cases 2 and 4 of Theorem 22.
	 */
	public static void main(String[] args) {
		for (int r = 2; r < 6; r++) {
			System.out.println("There are " + countGoodFunctions(r) + " binary block-additive sequences of rank " + r + ".");
		}
	}
}
