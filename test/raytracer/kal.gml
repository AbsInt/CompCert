% kal.gml

1.0 0.7 0.7 point /red
0.7 1.0 0.7 point /green
0.7 0.7 1.0 point /blue

{ /color
  { /v /u /face
    color 0.1 0.99 1.0
  }
} /mirror

                                % a cube
{ /v /u /face                     % bind arguments
  0.9 1.0 0.9 point               % surface color
  0.1 0.9 1.0                     % kd ks n
} cube

0.0 -0.5 35.0 translate
                                % a sphere
{ /v /u /face                     % bind arguments
  0.9 0.9 1.0 point               % surface color
  0.1 0.9 1.0                     % kd ks n
} sphere

-1.0 0.0 20.0 translate

union
                                % a sphere
{ /v /u /face                     % bind arguments
  1.0 1.0 0.9 point               % surface color
  0.1 0.9 1.0                     % kd ks n
} cylinder
20.0 rotatex
0.5 0.5 15.0 translate
union 

blue mirror apply plane
0.0 -2.0 0.0 translate

union

green mirror apply plane
0.0 -2.0 0.0 translate
120.0 rotatez

union

red mirror apply plane
0.0 -2.0 0.0 translate
240.0 rotatez

union

{ /v /u /face
  0.4 0.4 0.4 point
  0.0 0.0 1.0
} plane

90.0 rotatex
0.0 0.0 3.0 translate
difference

0.0 -1.0 0.0 translate

/scene

0.0 0.0 -2.0 point 0.9 0.9 0.9 point pointlight /light1

0.4 0.4	0.4 point	% ambient
[light1]		% lights
scene			% object
1000			% depth
90.0			% fov
400 400 		% wid ht
"kal.ppm"		% output file
render

