method Triple(x:int) returns (r:int)
  ensures r>=3*x
{
  if(0 <= x)
  {
    var y := Double(x);
    r := x + y;
  } else {
    var y := Double(-x);
    r := x + y;
  }
}

method Double(x:int) returns (r:int)
  requires 0 <= x
  ensures r >= 2*x
{
  r := x + x;
}

function Sum(x:nat): nat
requires x >= 0
decreases x - 1
{
  if x == 0 then 0 else x + Sum (x - 1)
}

method ComputeBigger(x:int, y:int) returns (b:int)
requires x != y
ensures b == y ==> y > x && b == x ==> x > y
{
  if x > y
  {
    b := x;
  }
  else
  {
    b := y;
  }
}

method ComputeSum(x: nat) returns (s: nat)
ensures s == Sum(x)
{
  s := 0;
  
  var cnt := 0;

  while cnt != x
    decreases x - cnt
    invariant 0 <= cnt <= x
    invariant s == Sum(cnt)
  {
    cnt := cnt + 1;
    s := s + cnt;
  }
}