# *DSLDoodle*: An Interactive Teaching Tool for Designing and Visualising DSLs

A simple interactive teaching tool that allows students to design their Domain-Specific Languages (DSLs) while simultaneously visualising the underlying data structures.

## Using DSLDoodle

### Setting up a virtual environment (for Linux):

DSLDoodle requires several dependencies. It is recommended to first set up a virtual environment. 

1) ```pip install virtualenv```
2) ```virtualenv venv```
3) ```source venv/bin/activate``` 

### Installing requirements:

```python3 -m pip install -r requirements.txt```

### Running the Application

```python3 dsldoodlev7.py```

### Designing DSLs

DSLDoodle helps to design Domain Specific Languages using Ply with Python. Example inputs for the program can be found in the tests folder. 


## Disclaimer

The DSLs that the tool can process are constrained. Using the Technology Acceptance Model, the tool was built with the intention of evaluating if such tools like this will help can be used as a supplement in Compiler Theory courses to boost student engagement and foster a deeper understanding of Compiler Theory.
