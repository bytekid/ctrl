/* equivalence sum sum1 [x1 >= 0] */

int sum(int n) {
  if (n <= 0) return 0;
  return n + sum(n-1);
}

