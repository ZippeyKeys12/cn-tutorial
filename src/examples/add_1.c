int add(int x, int y)
/* --BEGIN-- */
/*@ requires let Sum = (i64) x + (i64) y;
             -2147483648i64 <= Sum; Sum <= 2147483647i64;
    ensures return == (i32) Sum;
@*/
/* --END-- */
{
  return x+y;
}
