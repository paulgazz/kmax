#include <Python.h>
#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>

int main(int, char **);

static PyObject *ExtractorError;

static PyObject * kextract(PyObject *self, PyObject *args) {
  const char *outfile;
  const char *arch;
  const char *srcarch;

  if (!PyArg_ParseTuple(args, "s|s|s", &outfile, &arch, &srcarch)) {
    return NULL;
  }

  const char *cargs[] = {
    "kextractor", "--extract", "-o", outfile, "-e", arch, "-e", srcarch, "-e", "KERNELVERSION=kcu", "-e", "srctree=./", "-e", "CC=cc", "-e", "LD=ld", "Kconfig"
  };
  
  int errcode = main(16, cargs);

  return Py_BuildValue("i", errcode);
}

static char kextract_docs[] =
  "kextract( ): Extract Kconfig dependencies\n";

static PyMethodDef kextractor_funcs[] = {
  {"kextract", (PyCFunction)kextract, METH_VARARGS, kextract_docs},
  {NULL}
};

void initkextractor(void) {
  PyObject *m;
  
  m = Py_InitModule3("kextractor", kextractor_funcs,
                 "Extract Kconfig dependencies.");
  ExtractorError = PyErr_NewException("kextractor.error", NULL, NULL);
  Py_INCREF(ExtractorError);
  PyModule_AddObject(m, "error", ExtractorError);
}
