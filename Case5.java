public class Case5 {
	/**
	 * Each function F is a sum of a *high* part H and a *low* part L, associated
	 * with sequences f, h, l: we have h_n = f_{n - n mod 9} and l_n = f_n - h_n
	 * 
	 * FUNCTION: array representing H: its k-th entry is the result of applying f to
	 * a tuple that is the little-endian base-3 representation of k+9
	 * 
	 * FASTFUNCTION: stores the value of H on 4-tuples of base-3 digits (represented
	 * as pairs of base-9 digits)
	 * 
	 * LOWFUNCTION: array representing L: its k-th entry is the result of appliyng f
	 * to a tuple that is the little-endian base-3 representation of k
	 * 
	 * RESULT: array whose k-th entry is h_k
	 * 
	 * LOWRESULT: array whose k-th entry is l_k
	 * 
	 * DIGITS: 2D-array storing base-3 representations of integers with at most 8
	 * base-3 digits
	 * 
	 */
	private static final int[] FUNCTION = new int[18];
	private static final int[][] FASTFUNCTION = new int[9][9];
	private static final int[] LOWFUNCTION = new int[9];
	private static final int[] RESULT = new int[6561];
	private static final int[] LOWRESULT = new int[6561];
	private static final int[][] DIGITS = new int[6561][8];

	private static boolean start = true;

	/**
	 * Looks for the next high function. We discard arrays whose least non-zero
	 * entry is a 2, thereby avoiding to consider functions that are non-zero
	 * multiples of each other.
	 */
	private static boolean next() {
		for (int i = 0; i < 18; i++) {
			switch (FUNCTION[i]) {
			case 0:
				FUNCTION[i] = 1;
				return true;
			case 1:
				FUNCTION[i] = 2;
				return next();
			case 2:
				FUNCTION[i] = 0;
			}
		}
		return false;
	}

	/**
	 * Initialise LOWFUNCTION to be 0
	 */
	private static void init() {
		start = true;
		for (int i = 0; i < 9; i++) {
			LOWFUNCTION[i] = 0;
		}
	}

	/**
	 * Increment the integer whose base-3 little-endian representation is
	 * LOWFUNCTION.
	 */
	private static boolean lowNext() {
		if (start) {
			start = false;
			return true;
		}
		for (int i = 1; i < 9; i++) {
			switch (LOWFUNCTION[i]) {
			case 0:
			case 1:
				LOWFUNCTION[i]++;
				return true;
			case 2:
				LOWFUNCTION[i] = 0;
			}
		}
		return false;
	}

	/**
	 * Write the base-9 digits of n
	 */
	private static void digits() {
		for (int n = 0; n < 6561; n++) {
			int m = n;
			for (int i = 0; i < 8; i++) {
				DIGITS[n][i] = m % 9;
				m /= 9;
			}
		}
	}

	/**
	 * Evaluate a rank-3 block function on a 3-tuple
	 */
	private static int eval(int a, int b, int c) {
		return a == 0 ? 0 : FUNCTION[9 * (a - 1) + 3 * b + c];
	}

	/**
	 * Store the values on the function on all 2-tuples of base-9 digits (which
	 * represent 4-tuples of base-3 digits)
	 */
	private static void initFastFunction() {
		for (int a = 0; a < 3; a++) {
			for (int b = 0; b < 3; b++) {
				for (int c = 0; c < 3; c++) {
					for (int d = 0; d < 3; d++) {
						FASTFUNCTION[a + b * 3][c + d * 3] = eval(a, b, c) + eval(b, c, d);
					}
				}
			}
		}
	}

	/**
	 * Compute h_n
	 */
	private static int high(int n) {
		int result = 0;
		for (int i = 0; i < 7; i++) {
			result += FASTFUNCTION[DIGITS[n][i]][DIGITS[n][i + 1]];
		}
		return result % 3;
	}

	/**
	 * Compute l_n
	 */
	private static int low(int n) {
		return (DIGITS[n][0] % 3 == 0)
				? LOWFUNCTION[3 * (DIGITS[n][0] / 3) + (DIGITS[n][1] % 3)] + LOWFUNCTION[DIGITS[n][0] / 3]
				: 0;
	}

	/**
	 * 
	 * Looks for a witness that f is 3-correlated for a given delta = (0,a,b).
	 * 
	 * @param low: true if we are considering f = h + l, false if we just consider h
	 */
	private static boolean has3Correlation(int a, int b, int m, boolean low) {
		int M = m / 9;
		int[][] classes = new int[3][3];
		for (int i = 0; i < m - b; i++) {
			if (i / M == (i + b) / M) {
				int u = (RESULT[i + a] - RESULT[i] + (low ? LOWRESULT[i + a] - LOWRESULT[i] : 0) + 6) % 3;
				int v = (RESULT[i + b] - RESULT[i] + (low ? LOWRESULT[i + b] - LOWRESULT[i] : 0) + 6) % 3;
				classes[u][v]++;
				if (classes[u][v] > M) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * Looks for a witness that f is 3-correlated. When low = false, we just
	 * consider the high part of f, and focus only on tuples delta = (0,a,b) where 9
	 * divides a and b. We check such tuples where b < v (or b < 9v when low =
	 * false).
	 */
	private static boolean has3Correlation(int v, int m, boolean low) {
		for (int i = 0; i < m; i++) {
			if (low) {
				LOWRESULT[i] = low(i);
			} else {
				RESULT[i] = high(i);
			}
		}
		for (int b = 2; b < v; b++) {
			for (int a = 1; a < b; a++) {
				if (!has3Correlation(low ? a : 9 * a, low ? b : 9 * b, m, low)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Looks for a witness that all functions are 3-correlated. We first look at
	 * high parts and use tuples (0,9a,9b) where b < u. If no witness was found, we
	 * include low parts and use tuples (0,a,b) where b < v.
	 */
	private static void allDefect(int u, int v) {
		int B4 = 81;
		int B5 = 243;
		int B6 = 729;
		int B7 = 2187;
		int B8 = 6561;
		if (!has3Correlation(u, B6, false) && !has3Correlation(u, B7, false) && !has3Correlation(u, B8, false)) {
			init();
			while (lowNext()) {
				if (!has3Correlation(v, B4, true) && !has3Correlation(v, B5, true) && !has3Correlation(v, B6, true)) {
					throw new RuntimeException("Classification problem!");
				}
			}
		}
	}

	/**
	 * Checks case 5 of Theorem 22.
	 */
	public static void main(String[] args) {
		digits();
		while (next()) {
			initFastFunction();
			allDefect(5, 6);
		}
	}
}
