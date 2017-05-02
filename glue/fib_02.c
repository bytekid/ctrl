int fastfib(int n) {
  int i, result, old_result, temp;
  if (!n) return 0;

  result = 1;
  old_result = 0;

  for (i = 2; i <= n; i++) {
    temp = result;
    result = result + old_result;
    old_result = temp;
  }

  return result;
}

