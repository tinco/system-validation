#!/bin/bash

export HW2CP=/opt/sfw/generic/jmlunitng-1.3/lib/jmlunitng.jar:/opt/sfw/generic/JML-5.6_rc4/bin/jmlruntime.jar

# After this, the commands that you can run are:
# 
# To generate the tests:
#   jmlunitng --package --rac-version jml2 --dest tests --reflection src
# 
# To compile the source:
#   jmlc src/
# 
# (At this point you edit the generated files to provide test data)
# 
# To compile the test suite:
#   javac -cp $HW2CP:src tests/*.java
#
# To run the test suite:
#   java -cp $HW2CP:tests:src com.beust.testng.TestNG test_movePlayer.xml
#
# Then to view test results:
#   firefox "test-output/System Validation 2012 Homework 2/movePlayer.html"
#




