public class Case3 {
	/**
	 * Each function F is represented by an array whose k-th entry is the value of F
	 * on the little-endian base-3 representation of k (with 3 digits)
	 * 
	 * PARAMETER: representation of F
	 * 
	 * POW3: powers of 3 (POW3[k] = 3^k)
	 * 
	 * MAX: maximal possible values of PARAMETER's entries. They are set to 0 at 0
	 * and powers and doubles of powers of 3, to check once each family of functions
	 * whose differences are sums of projection-selections
	 * 
	 * NMAX: 15, the maximal number of base-3 digits of the numbers we investigate
	 * 
	 * N: base-3 little-endian representation of the current integer n
	 * 
	 * SHIFTS: integers whose non-zero binary digits are at positions 1, 2, 4, 8 and
	 * 16
	 */
	private static final int[] POW3 = { 1, 3, 9, 27, 81, 243, 729, 2187, 6561, 19683, 59049, 177147, 531441, 1594323,
			4782969 };
	private static final int[] MAX = new int[] { 0, 0, 0, 0, 2, 2, 0, 2, 2, 0, 2, 2, 2, 2, 2, 2, 2, 2, 0, 2, 2, 2, 2, 2,
			2, 2, 2 };
	private static final int[] PARAMETER = new int[27];

	private static final int NMAX = 15;
	private static final int[] N = new int[NMAX + 2];

	private static boolean start = true;

	/**
	 * Evaluate a rank-3 block function on a 3-tuple
	 */
	private static int f(int a, int b, int c) {
		return PARAMETER[a + 3 * b + 9 * c];
	}

	/**
	 * Looks for the next function. We discard arrays whose least non-zero entry is
	 * a 2, thereby avoiding to consider functions that are non-zero multiples of
	 * each other.
	 */
	private static boolean next() {
		if (start) {
			start = false;
			return true;
		}
		for (int i = 0; i < 27; i++) {
			if (PARAMETER[i] == MAX[i]) {
				PARAMETER[i] = 0;
			} else if (PARAMETER[i] == 0) {
				PARAMETER[i] = 1;
				return true;
			} else {
				PARAMETER[i] = 2;
				return next();
			}
		}
		return false;
	}

	/**
	 * Compute u_n
	 */
	private static int eval(int n) {
		for (int i = 0; i < NMAX; i++) {
			N[i] = (n % 3);
			n /= 3;
		}
		int result = 0;
		for (int i = 0; i < NMAX; i++) {
			result += f(N[i], N[i + 1], N[i + 2]);
		}
		return result % 3;
	}

	/**
	 * 
	 * Looks for a witness that f is 2-correlated for a given delta = (0,a).
	 */
	private static boolean has2Correlation(int a, int[] classes) {
		var tab = new int[3];
		var small = classes.length / 27;
		for (var n = 0; n + a < classes.length; n++) {
			if (small > 0 && n / small == (n + a) / small) {
				tab[(2 * classes[n] + classes[n + a]) % 3]++;
			}
		}
		return Math.max(tab[0], Math.max(tab[1], tab[2])) > (classes.length / 3);
	}

	/**
	 * Looks for a witness that (u_n) is 2-correlated, by checking all parameters m
	 * < NMAX and all vectors delta = (0,a) with Kmin <= a < Kmax.
	 */
	private static boolean has2Correlation(int Kmin, int Kmax) {
		for (int m = 2; m < NMAX; m++) {
			int M = POW3[m];
			var classes = new int[M];
			for (var i = 0; i < M; i++) {
				classes[i] = eval(i);
			}
			for (var a = Kmin; a < Kmax; a++) {
				if (has2Correlation(a, classes)) {
					return true;
				}
			}
		}
		return false;
	}

	/**
	 * Checks whether F is (before,after)-strongly 2-uncorrelated.
	 */
	private static boolean goodFamily(int before, int after) {
		for (var len = 0; len < before + 2; len++) {
			var eq = new boolean[len + after + 1];
			var xBuffer = new int[len + after + 1];
			var yBuffer = new int[len + after + 1];
			var pad = Math.max(len + 1 - before, 0);
			for (var i = 0; i < (1 << len); i += 1 << pad) {
				for (var j = 0; j < len; j++) {
					eq[j] = ((i >> j) & 1) != 0;
				}
				for (var j = len + 1; j < len + after + 1; j++) {
					eq[j] = true;
				}
				if (!family(eq, xBuffer, yBuffer, 0, pad, len)) {
					return false;
				}
			}
		}
		return true;
	}

	/**
	 * 
	 * Investigates a subset of the families F(x,y)
	 * 
	 * @param eq:      bitmask indicating at which positions x and y must coincide
	 * @param offset:  positions at which x and y already have fixed 
	 * @param pad:     weight of the families
	 * @param xBuffer: vector x
	 * @param yBuffer: vector y
	 * @param len:     carry distance of x and y
	 */
	private static boolean family(boolean[] eq, int[] xBuffer, int[] yBuffer, int offset, int pad, int len) {
		if (offset == eq.length) {
			var tab = new int[3];
			fill(eq, xBuffer, yBuffer, pad, tab);
			return tab[0] == tab[1] && tab[1] == tab[2];
		}
		if (eq[offset]) {
			return family(eq, xBuffer, yBuffer, offset + 1, pad, len);
		}
		for (var i = 0; i < 3; i++) {
			for (var j = 0; j < 3; j++) {
				if ((offset != len && offset < pad) || i != j) {
					xBuffer[offset] = i;
					yBuffer[offset] = j;
					if (!family(eq, xBuffer, yBuffer, offset + 1, pad, len)) {
						return false;
					}
				}
			}
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
			tab[(2 * value(xBuffer) + value(yBuffer)) % 3]++;
		} else if (eq[offset]) {
			for (var i = 0; i < 3; i++) {
				xBuffer[offset] = i;
				yBuffer[offset] = i;
				fill(eq, xBuffer, yBuffer, offset + 1, tab);
			}
		} else {
			fill(eq, xBuffer, yBuffer, offset + 1, tab);
		}
	}

	/**
	 * Computes f(x)
	 */
	private static int value(int[] xBuffer) {
		int sum = 0;
		for (int i = 0; i + 2 < xBuffer.length; i++) {
			sum += f(xBuffer[i], xBuffer[i + 1], xBuffer[i + 2]);
		}
		return sum;
	}

	public static void main(String[] args) {
		long good = 0;
		long mult = 2 * POW3[6];
		while (next()) {
			if (goodFamily(0, 2)) {
				good++;
			} else if (!has2Correlation(1, 7) && !has2Correlation(7, 10)) {
				throw new RuntimeException("Classification problem!");
			}
		}
		System.out.println("We found " + (mult * good) + " functions.");
	}
}
