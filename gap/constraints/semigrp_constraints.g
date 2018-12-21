
# Some constraints for semigroups

# Compute the stabilizer of a transformation under conjugation
BTKit_Con.TransCentralizer := function(n, fixedelt)
    local
        imgpart, kernelpart,
        cycles, cyclepart,
          i, c, s, r,
          fixByFixed, pointMap;

    imgpart := ImageListOfTransformation(fixedelt);
    kernelpart := FlatKernelOfTransformation(fixedelt, n);

    fixByFixed := function(pointlist)
        local part, s, p;
        part := [1..n] * 0;
        s := 1;
        for p in pointlist do
            if part[p] = 0 then
                repeat
                    part[p] := s;
                    p := p ^ fixedelt;
                    s := s + 1;
                until part[p] <> 0;
            fi;
        od;
        return part;
    end;

    r := rec( name := "TransCentralizer",
              check := {p} -> fixedelt ^ p = fixedelt,
              refine := rec( initalise := function(ps)
                               local points;
                               points := fixByFixed(PS_FixedPoints(ps));
                               # Pass cyclepart just on the first call, for efficency
                               return [ rec(partition := {x} -> imgpart[x])
                                      , rec(partition := {x} -> kernelpart[x])
                                      , rec(partition := {x} -> points[x])];
                             end,
                             changed := function(ps, rbase)
                               local points;
                               points := fixByFixed(PS_FixedPoints(ps));
                               return [ rec(partition := {x} -> imgpart[x])
                                      , rec(partition := {x} -> kernelpart[x])
                                      , rec(partition := {x} -> points[x]) ];
                             end) );
    return r;
end;


BTKit_Con.TransformationSemigroupNormalizer := function(n, semigrp)
    local
        gens,
        imgpart, kernelpart,
        cycles, cyclepart,
          i, c, s, r,
          fixByFixed, pointMap;

    # We need both the generators and the semigroup, because
    # the semigroup might have better information for 
    # element tests.
    gens := GeneratorsOfSemigroup(semigrp);

    imgpart := ImageListOfTransformation(fixedelt);
    kernelpart := FlatKernelOfTransformation(fixedelt, n);

    fixByFixed := function(pointlist)
        local part, s, p;
        part := [1..n] * 0;
        s := 1;
        for p in pointlist do
            if part[p] = 0 then
                repeat
                    part[p] := s;
                    p := p ^ fixedelt;
                    s := s + 1;
                until part[p] <> 0;
            fi;
        od;
        return part;
    end;

    r := rec( name := "TransCentralizer",
              check := {p} -> ForAll(gens, g -> g^p in semigrp),
              refine := rec( initalise := function(ps)
                               local points;
                               points := fixByFixed(PS_FixedPoints(ps));
                               # Pass cyclepart just on the first call, for efficency
                               return [ rec(partition := {x} -> imgpart[x])
                                      , rec(partition := {x} -> kernelpart[x])
                                      , rec(partition := {x} -> points[x])];
                             end,
                             changed := function(ps, rbase)
                               local points;
                               points := fixByFixed(PS_FixedPoints(ps));
                               return [ rec(partition := {x} -> imgpart[x])
                                      , rec(partition := {x} -> kernelpart[x])
                                      , rec(partition := {x} -> points[x]) ];
                             end) );
    return r;
end;

