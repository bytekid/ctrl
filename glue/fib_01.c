int fastfib(int num){
  int f0,f1,f2;

  for(f0=f1=1;num>=2;num--){
    f2=f1+f0;
    f0=f1;
    f1=f2;
  }

  return f1;

}

