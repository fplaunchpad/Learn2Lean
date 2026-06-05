// Lean compiler output
// Module: Arithmetic_Formalization.Division
// Imports: public import Init public import Arithmetic_Formalization.Foundations public import Arithmetic_Formalization.Multiplication
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lp_Arithmetic__Formalization_mulTable(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_findQuotientDigitHelper(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_findQuotientDigitHelper___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_findQuotientDigit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_findQuotientDigit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_trimTrailingZeros(lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_longDivHelper(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_longDivHelper___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_longDiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_longDiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__3_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__trimTrailingZeros_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__trimTrailingZeros_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__trimTrailingZeros_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__trimTrailingZeros_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__longDivHelper_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__longDivHelper_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__longDivHelper_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__longDivHelper_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_findQuotientDigitHelper(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_nat_add(x_7, x_6);
x_9 = lean_unsigned_to_nat(10u);
x_10 = lean_nat_dec_lt(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lp_Arithmetic__Formalization_mulTable(x_8, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec_ref(x_11);
x_14 = lean_nat_mul(x_9, x_13);
lean_dec(x_13);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
x_16 = lean_nat_dec_le(x_15, x_1);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_8);
x_3 = x_7;
goto _start;
}
else
{
lean_dec(x_7);
return x_8;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_findQuotientDigitHelper___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_Arithmetic__Formalization_findQuotientDigitHelper(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_findQuotientDigit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(9u);
x_4 = lp_Arithmetic__Formalization_findQuotientDigitHelper(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_findQuotientDigit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_Arithmetic__Formalization_findQuotientDigit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_trimTrailingZeros(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
return x_1;
}
else
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lp_Arithmetic__Formalization_trimTrailingZeros(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_dec_eq(x_3, x_6);
if (x_7 == 0)
{
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_free_object(x_1);
lean_dec(x_3);
return x_5;
}
}
else
{
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_1);
x_10 = lp_Arithmetic__Formalization_trimTrailingZeros(x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_8, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_dec(x_8);
return x_10;
}
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_longDivHelper(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_8 = lean_unsigned_to_nat(10u);
x_9 = lean_nat_mul(x_3, x_8);
lean_dec(x_3);
x_10 = lean_nat_add(x_9, x_6);
lean_dec(x_6);
lean_dec(x_9);
x_11 = lp_Arithmetic__Formalization_findQuotientDigit(x_10, x_2);
x_12 = lp_Arithmetic__Formalization_mulTable(x_11, x_2);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_nat_mul(x_8, x_14);
lean_dec(x_14);
x_16 = lean_nat_add(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
x_17 = lean_nat_sub(x_10, x_16);
lean_dec(x_16);
lean_dec(x_10);
x_18 = lp_Arithmetic__Formalization_longDivHelper(x_7, x_2, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
lean_ctor_set(x_1, 1, x_20);
lean_ctor_set(x_1, 0, x_11);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_18, 0);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_18);
lean_ctor_set(x_1, 1, x_21);
lean_ctor_set(x_1, 0, x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(10u);
x_27 = lean_nat_mul(x_3, x_26);
lean_dec(x_3);
x_28 = lean_nat_add(x_27, x_24);
lean_dec(x_24);
lean_dec(x_27);
x_29 = lp_Arithmetic__Formalization_findQuotientDigit(x_28, x_2);
x_30 = lp_Arithmetic__Formalization_mulTable(x_29, x_2);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_nat_mul(x_26, x_32);
lean_dec(x_32);
x_34 = lean_nat_add(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
x_35 = lean_nat_sub(x_28, x_34);
lean_dec(x_34);
lean_dec(x_28);
x_36 = lp_Arithmetic__Formalization_longDivHelper(x_25, x_2, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_29);
lean_ctor_set(x_40, 1, x_37);
if (lean_is_scalar(x_39)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_39;
}
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_38);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_longDivHelper___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_Arithmetic__Formalization_longDivHelper(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_longDiv(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_List_reverse___redArg(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lp_Arithmetic__Formalization_longDivHelper(x_3, x_2, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = l_List_reverse___redArg(x_7);
x_9 = lp_Arithmetic__Formalization_trimTrailingZeros(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = l_List_reverse___redArg(x_10);
x_13 = lp_Arithmetic__Formalization_trimTrailingZeros(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization_longDiv___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_Arithmetic__Formalization_longDiv(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_1, x_4);
if (x_5 == 1)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_box(0);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_1, x_8);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__3_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__3_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_2, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_sub(x_2, x_9);
x_11 = lean_apply_1(x_4, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__3_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__3_splitter(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__findQuotientDigitHelper_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__trimTrailingZeros_match__4_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_2(x_3, x_6, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__trimTrailingZeros_match__4_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec_ref(x_2);
x_9 = lean_apply_2(x_4, x_7, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__trimTrailingZeros_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_box(0);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__trimTrailingZeros_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_box(0);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__longDivHelper_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; 
lean_dec(x_5);
x_6 = lean_apply_2(x_4, x_2, x_3);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec_ref(x_1);
x_9 = lean_apply_4(x_5, x_7, x_8, x_2, x_3);
return x_9;
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__longDivHelper_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; 
lean_dec(x_6);
x_7 = lean_apply_2(x_5, x_3, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_apply_4(x_6, x_8, x_9, x_3, x_4);
return x_10;
}
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__longDivHelper_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_Arithmetic__Formalization___private_Arithmetic__Formalization_Division_0__longDivHelper_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Arithmetic__Formalization_Arithmetic__Formalization_Foundations(uint8_t builtin);
lean_object* initialize_Arithmetic__Formalization_Arithmetic__Formalization_Multiplication(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Arithmetic__Formalization_Arithmetic__Formalization_Division(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Arithmetic__Formalization_Arithmetic__Formalization_Foundations(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Arithmetic__Formalization_Arithmetic__Formalization_Multiplication(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
