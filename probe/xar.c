#include <stdio.h>
#include <stdint.h>
#include <string.h>
typedef unsigned __int128 u128;
static u128 hx(const char*s){u128 v=0;for(;*s;s++){int c=*s;v=v*16+(c<='9'?c-'0':c-'a'+10);}return v;}
static void pr(const char*tag,u128 v){printf("%s 0x%016llx%016llx\n",tag,(unsigned long long)(v>>64),(unsigned long long)v);}
static u128 f_0_1_1(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #1\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_1_7(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #7\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_1_8(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #8\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_1_12(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #12\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_1_16(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #16\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_1_20(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #20\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_1_24(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #24\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_1_25(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #25\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_1_31(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #31\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_1_32(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #32\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_2_1(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #1\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_2_7(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #7\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_2_8(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #8\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_2_12(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #12\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_2_16(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #16\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_2_20(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #20\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_2_24(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #24\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_2_25(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #25\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_2_31(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #31\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_2_32(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #32\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_0_1(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #1\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_0_7(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #7\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_0_8(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #8\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_0_12(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #12\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_0_16(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #16\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_0_20(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #20\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_0_24(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #24\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_0_25(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #25\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_0_31(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #31\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_0_0_32(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #32\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_1_1(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #1\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_1_7(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #7\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_1_8(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #8\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_1_12(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #12\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_1_16(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #16\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_1_20(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #20\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_1_24(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #24\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_1_25(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #25\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_1_31(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #31\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_1_32(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z1.s, #32\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_2_1(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #1\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_2_7(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #7\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_2_8(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #8\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_2_12(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #12\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_2_16(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #16\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_2_20(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #20\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_2_24(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #24\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_2_25(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #25\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_2_31(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #31\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_2_32(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z2.s, #32\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_0_1(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #1\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_0_7(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #7\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_0_8(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #8\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_0_12(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #12\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_0_16(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #16\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_0_20(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #20\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_0_24(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #24\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_0_25(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #25\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_0_31(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #31\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
static u128 f_1_0_32(u128 a,u128 b,u128 c){u128 o;__asm__ volatile("ldr q0,[%1]\n ldr q1,[%2]\n ldr q2,[%3]\n xar z0.s, z0.s, z0.s, #32\n str q0,[%0]\n"::"r"(&o),"r"(&a),"r"(&b),"r"(&c):"v0","v1","v2","memory");return o;}
int main(void){
 unsigned long vl; __asm__ volatile("cntb %0":"=r"(vl)); printf("cntb %lu\n",vl);
 u128 a0=hx("47be5543e684460b8caafc59aff91663"),b0=hx("d5b39162c1984cc4c9c6de1db050fcb1"),c0=hx("183bb3b2f27fe16536ca734e082da43c");
 u128 a1=hx("55eadb18f6d1d81649d2bf3ef06dbe6f"),b1=hx("db26ce183543c96b9f9eb90b2c4563c4"),c1=hx("384a612f2df0168eeee920eaf4a28fec");
 pr("run 0 z1 #1", f_0_1_1(a0,b0,c0));
 pr("run 0 z1 #7", f_0_1_7(a0,b0,c0));
 pr("run 0 z1 #8", f_0_1_8(a0,b0,c0));
 pr("run 0 z1 #12", f_0_1_12(a0,b0,c0));
 pr("run 0 z1 #16", f_0_1_16(a0,b0,c0));
 pr("run 0 z1 #20", f_0_1_20(a0,b0,c0));
 pr("run 0 z1 #24", f_0_1_24(a0,b0,c0));
 pr("run 0 z1 #25", f_0_1_25(a0,b0,c0));
 pr("run 0 z1 #31", f_0_1_31(a0,b0,c0));
 pr("run 0 z1 #32", f_0_1_32(a0,b0,c0));
 pr("run 0 z2 #1", f_0_2_1(a0,b0,c0));
 pr("run 0 z2 #7", f_0_2_7(a0,b0,c0));
 pr("run 0 z2 #8", f_0_2_8(a0,b0,c0));
 pr("run 0 z2 #12", f_0_2_12(a0,b0,c0));
 pr("run 0 z2 #16", f_0_2_16(a0,b0,c0));
 pr("run 0 z2 #20", f_0_2_20(a0,b0,c0));
 pr("run 0 z2 #24", f_0_2_24(a0,b0,c0));
 pr("run 0 z2 #25", f_0_2_25(a0,b0,c0));
 pr("run 0 z2 #31", f_0_2_31(a0,b0,c0));
 pr("run 0 z2 #32", f_0_2_32(a0,b0,c0));
 pr("run 0 z0 #1", f_0_0_1(a0,b0,c0));
 pr("run 0 z0 #7", f_0_0_7(a0,b0,c0));
 pr("run 0 z0 #8", f_0_0_8(a0,b0,c0));
 pr("run 0 z0 #12", f_0_0_12(a0,b0,c0));
 pr("run 0 z0 #16", f_0_0_16(a0,b0,c0));
 pr("run 0 z0 #20", f_0_0_20(a0,b0,c0));
 pr("run 0 z0 #24", f_0_0_24(a0,b0,c0));
 pr("run 0 z0 #25", f_0_0_25(a0,b0,c0));
 pr("run 0 z0 #31", f_0_0_31(a0,b0,c0));
 pr("run 0 z0 #32", f_0_0_32(a0,b0,c0));
 pr("run 1 z1 #1", f_1_1_1(a1,b1,c1));
 pr("run 1 z1 #7", f_1_1_7(a1,b1,c1));
 pr("run 1 z1 #8", f_1_1_8(a1,b1,c1));
 pr("run 1 z1 #12", f_1_1_12(a1,b1,c1));
 pr("run 1 z1 #16", f_1_1_16(a1,b1,c1));
 pr("run 1 z1 #20", f_1_1_20(a1,b1,c1));
 pr("run 1 z1 #24", f_1_1_24(a1,b1,c1));
 pr("run 1 z1 #25", f_1_1_25(a1,b1,c1));
 pr("run 1 z1 #31", f_1_1_31(a1,b1,c1));
 pr("run 1 z1 #32", f_1_1_32(a1,b1,c1));
 pr("run 1 z2 #1", f_1_2_1(a1,b1,c1));
 pr("run 1 z2 #7", f_1_2_7(a1,b1,c1));
 pr("run 1 z2 #8", f_1_2_8(a1,b1,c1));
 pr("run 1 z2 #12", f_1_2_12(a1,b1,c1));
 pr("run 1 z2 #16", f_1_2_16(a1,b1,c1));
 pr("run 1 z2 #20", f_1_2_20(a1,b1,c1));
 pr("run 1 z2 #24", f_1_2_24(a1,b1,c1));
 pr("run 1 z2 #25", f_1_2_25(a1,b1,c1));
 pr("run 1 z2 #31", f_1_2_31(a1,b1,c1));
 pr("run 1 z2 #32", f_1_2_32(a1,b1,c1));
 pr("run 1 z0 #1", f_1_0_1(a1,b1,c1));
 pr("run 1 z0 #7", f_1_0_7(a1,b1,c1));
 pr("run 1 z0 #8", f_1_0_8(a1,b1,c1));
 pr("run 1 z0 #12", f_1_0_12(a1,b1,c1));
 pr("run 1 z0 #16", f_1_0_16(a1,b1,c1));
 pr("run 1 z0 #20", f_1_0_20(a1,b1,c1));
 pr("run 1 z0 #24", f_1_0_24(a1,b1,c1));
 pr("run 1 z0 #25", f_1_0_25(a1,b1,c1));
 pr("run 1 z0 #31", f_1_0_31(a1,b1,c1));
 pr("run 1 z0 #32", f_1_0_32(a1,b1,c1));
 return 0;}
