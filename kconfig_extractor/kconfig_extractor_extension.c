#include <Python.h>
#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>

int main(int, char **);

static PyObject *ExtractorError;

static PyObject * extract_kconfig(PyObject *self, PyObject *args) {
  const char *outfile;
  const char *arch;
  const char *srcarch;

  if (!PyArg_ParseTuple(args, "s|s|s", &outfile, &arch, &srcarch)) {
    return NULL;
  }

  const char *cargs[] = {
    "kconfig_extractor", "--extract", "-o", outfile, "-e", arch, "-e", srcarch, "-e", "KERNELVERSION=kcu", "-e", "srctree=./", "-e", "CC=cc", "Kconfig"
  };
  
  int errcode = main(15, cargs);

  return Py_BuildValue("i", errcode);
}

static char extract_kconfig_docs[] =
  "extract_kconfig( ): Extract Kconfig dependencies\n";

static PyMethodDef kconfig_extractor_funcs[] = {
  {"extract_kconfig", (PyCFunction)extract_kconfig, METH_VARARGS, extract_kconfig_docs},
  {NULL}
};

void initkconfig_extractor(void) {
  PyObject *m;
  
  m = Py_InitModule3("kconfig_extractor", kconfig_extractor_funcs,
                 "Extract Kconfig dependencies.");
  ExtractorError = PyErr_NewException("kconfig_extractor.error", NULL, NULL);
  Py_INCREF(ExtractorError);
  PyModule_AddObject(m, "error", ExtractorError);
}
