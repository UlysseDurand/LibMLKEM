with SPARK.Big_Integers; use SPARK.Big_Integers;

package body Reference
    with SPARK_Mode => On
is

    function sum (A : Big_Integer ; B : Big_Integer ; F : Integer_Function_Access ) is
    (if A > B then 0 else sum (A, B - 1) + F (B));

end Reference;