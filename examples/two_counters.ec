node top
  (x: bool)
returns
  (OK: bool);

var
  V13_b: bool;
  V14_d: bool;
  V40_a: bool;
  V41_b: bool;
  V51_time: int;

let
  OK = (V13_b = V14_d);
  V13_b = (V40_a and V41_b);
  V14_d = (V51_time = 2);
  V40_a = (false -> (not (pre V41_b)));
  V41_b = (false -> (pre V40_a));
  V51_time = (0 -> (if ((pre V51_time) = 3) then 0 else ((pre V51_time) + 1)));

 
--%PROPERTY  OK;

tel;

