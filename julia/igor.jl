type Q
    n::UInt8
end

const Qinv = [Q(1),Q(2),Q(3),Q(4),Q(5),Q(6),Q(8),Q(7),Q(9),Q(10),Q(11),Q(13),Q(12),Q(14),Q(15),Q(16)]

const Qprod = [Q(1) Q(2) Q(3) Q(4) Q(5) Q(6) Q(7) Q(8) Q(9) Q(10) Q(11) Q(12) Q(13) Q(14) Q(15) Q(16);
               Q(2) Q(1) Q(6) Q(7) Q(8) Q(3) Q(4) Q(5) Q(12) Q(13) Q(14) Q(9) Q(10) Q(11) Q(16) Q(15);
               Q(3) Q(6) Q(1) Q(9) Q(10) Q(2) Q(12) Q(13) Q(4) Q(5) Q(15) Q(7) Q(8) Q(16) Q(11) Q(14);
               Q(4) Q(8) Q(9) Q(1) Q(11) Q(13) Q(14) Q(2) Q(3) Q(15) Q(5) Q(16) Q(6) Q(7) Q(10) Q(12);
               Q(5) Q(7) Q(10) Q(11) Q(1) Q(12) Q(2) Q(14) Q(15) Q(3) Q(4) Q(6) Q(16) Q(8) Q(9) Q(13);
               Q(6) Q(3) Q(2) Q(12) Q(13) Q(1) Q(9) Q(10) Q(7) Q(8) Q(16) Q(4) Q(5) Q(15) Q(14) Q(11);
               Q(7) Q(5) Q(12) Q(2) Q(14) Q(10) Q(11) Q(1) Q(6) Q(16) Q(8) Q(15) Q(3) Q(4) Q(13) Q(9);
               Q(8) Q(4) Q(13) Q(14) Q(2) Q(9) Q(1) Q(11) Q(16) Q(6) Q(7) Q(3) Q(15) Q(5) Q(12) Q(10);
               Q(9) Q(13) Q(4) Q(3) Q(15) Q(8) Q(16) Q(6) Q(1) Q(11) Q(10) Q(14) Q(2) Q(12) Q(5) Q(7);
               Q(10) Q(12) Q(5) Q(15) Q(3) Q(7) Q(6) Q(16) Q(11) Q(1) Q(9) Q(2) Q(14) Q(13) Q(4) Q(8);
               Q(11) Q(14) Q(15) Q(5) Q(4) Q(16) Q(8) Q(7) Q(10) Q(9) Q(1) Q(13) Q(12) Q(2) Q(3) Q(6);
               Q(12) Q(10) Q(7) Q(6) Q(16) Q(5) Q(15) Q(3) Q(2) Q(14) Q(13) Q(11) Q(1) Q(9) Q(8) Q(4);
               Q(13) Q(9) Q(8) Q(16) Q(6) Q(4) Q(3) Q(15) Q(14) Q(2) Q(12) Q(1) Q(11) Q(10) Q(7) Q(5);
               Q(14) Q(11) Q(16) Q(8) Q(7) Q(15) Q(5) Q(4) Q(13) Q(12) Q(2) Q(10) Q(9) Q(1) Q(6) Q(3);
               Q(15) Q(16) Q(11) Q(10) Q(9) Q(14) Q(13) Q(12) Q(5) Q(4) Q(3) Q(8) Q(7) Q(6) Q(1) Q(2);
               Q(16) Q(15) Q(14) Q(13) Q(12) Q(11) Q(10) Q(9) Q(8) Q(7) Q(6) Q(5) Q(4) Q(3) Q(2) Q(1)]

const Qname = [ "<id>", "c", "b", "f3", "a", "d", "c*f3", "c*a", "b*f3", "b*a",
                "f3*a", "d*f3", "d*a", "c*f3*a", "b*f3*a", "d*f3*a" ]

const Qname = [ "<id>", "f1", "f2", "f3", "f4", "f1*f2", "f1*f3", "f1*f4", "f2*f3", "f2*f4",
  "f3*f4", "f1*f2*f3", "f1*f2*f4", "f1*f3*f4", "f2*f3*f4", "f1*f2*f3*f4" ]

function Q(s::String)
    p = findfirst(Qname,s)
    if p==0 && s=="<identity> of ..."
        p = 1
    end
    p==0 && error("Bad string $s")
    Q(p)
end

import Base: *, ^, show

show(io::IO, a::Q) = print(io,Qname[a.n])

*(a::Q, b::Q) = Qprod[a.n,b.n]
^(a::Q, b::Q) = Qprod[Qinv[b.n].n,Qprod[a.n,b.n].n]

function ^(a::Q, b::Int)
    if b==0
        return Q(1)
    end 
    if b<0
        b = -b
        a = Qinv[a.n]
    end
    r = a
    while b>1
        r = Qprod[r.n,a.n]
        b -= 1
    end
    r
end

g = 3

orbits = Array{UInt8}(ntuple(i->16,2*g))

# check law is satisfied by generators
law(s)=s[1]^-1*s[1]^s[2]*s[3]^-1*s[3]^s[4]*s[5]^-1*s[5]^s[6]

generators = Any[]

for i=1:g
    push!(generators,eval(:(function(s)
          t = [s...]
          t[2*$i] = s[2*$i-1]*s[2*$i]
          (t...)
          end)))
    push!(generators,eval(:(function(s)
          t = [s...]
          t[2*$i-1] = s[2*$i]*s[2*$i-1]
          (t...)
          end)))
end

for i=1:g-1
    push!(generators,eval(:(function(s)
          t = [s...]
          x = s[2*$i]*s[2*$i+1]^-1
          t[2*$i-1:2*$i+2] = [x*s[2*$i-1],x*s[2*$i]*x^-1,x*s[2*$i+1]*x^-1,x*s[2*$i+2]]
          (t...)
          end)))
end

if false
orbits[:] = 0
done = 0
numorbits = 0
while orbits[im = indmin(orbits)]==0
    numorbits += 1
    queue = [ind2sub(orbits,im)]
    while !isempty(queue)
        s = pop!(queue)
        if orbits[s...] != numorbits
            orbits[s...] = numorbits
            done += 1
            if done % 10000 == 0
                print("$numorbits orbits for now, $(100*done/length(orbits))% done...\r")
            end
            for g in generators
                push!(queue,map(x->x.n,g(map(Q,s))))
            end
        end
    end
end

# save work
writedlm("orbits.Q6",orbits)
else
# read back
orbits = reshape(readdlm("orbits.Q6"),ntuple(i->16,6))
end

# all in Q^3x1^3, except
# map(Q,ind2sub(orbits,findfirst(orbits,86))) -> (b*a,f3,b,c,<id>,<id>)
# map(Q,ind2sub(orbits,findfirst(orbits,87))) -> (f3,<id>,b,<id>,c,<id>)
# map(Q,ind2sub(orbits,findfirst(orbits,88))) -> (f3*a,<id>,b,<id>,c,<id>)
# map(Q,ind2sub(orbits,findfirst(orbits,89))) -> (a,f3,b,<id>,c,<id>)
# map(Q,ind2sub(orbits,findfirst(orbits,90))) -> (a,<id>,f3,<id>,b,<id>)

true
