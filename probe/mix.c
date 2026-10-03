#include <stdio.h>
#include <time.h>
static double now(void){struct timespec t;clock_gettime(CLOCK_MONOTONIC,&t);return t.tv_sec*1e9+t.tv_nsec;}
void k_neon_full(long);
void k_sve_full(long);
void k_neon_vec(long);
void k_sve_vec(long);
void k_scalar(long);
int main(void){ long n=2000000;
 { double best=1e30; for(int r=0;r<7;r++){double t=now(); k_neon_full(n); t=now()-t; if(t<best)best=t;} printf("%-10s %4d instrs  %.2f ns/iter\n","neon_full",396,best/n); }
 { double best=1e30; for(int r=0;r<7;r++){double t=now(); k_sve_full(n); t=now()-t; if(t<best)best=t;} printf("%-10s %4d instrs  %.2f ns/iter\n","sve_full",324,best/n); }
 { double best=1e30; for(int r=0;r<7;r++){double t=now(); k_neon_vec(n); t=now()-t; if(t<best)best=t;} printf("%-10s %4d instrs  %.2f ns/iter\n","neon_vec",204,best/n); }
 { double best=1e30; for(int r=0;r<7;r++){double t=now(); k_sve_vec(n); t=now()-t; if(t<best)best=t;} printf("%-10s %4d instrs  %.2f ns/iter\n","sve_vec",132,best/n); }
 { double best=1e30; for(int r=0;r<7;r++){double t=now(); k_scalar(n); t=now()-t; if(t<best)best=t;} printf("%-10s %4d instrs  %.2f ns/iter\n","scalar",192,best/n); }
 return 0; }
