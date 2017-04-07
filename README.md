This is a Maven project implementing an ImageJ plugin providing trackig of 
a spot moving in a field with 4 reference marks. It was created for automatization 
of tracking of laser spot reflected from the mirror attached to the end of
a needle-like crystal bending as a result of photomechanical effect (photobending).
Photobending is a phenomenon of crystal deformation caused by non-uniform 
crystal structure transformation due to photochemical reaction. 

Required input is a stack of timelapse images of the spot moving relative to the 
template picture with 4 marks located in the corners of a square.
The output is the time dependence of spot dislacement given in units of the square 
side length. Usage of the template with 4 marks allows to compensate for the effects 
of picture instability and view perspective.

The project uses ideas and code of 
1. Template Matching by Qingzong Tseng (based on opencv)
2. Exif Metadata Library by Drew Noakes
