#include <Python.h>
#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>

int main(int, char **);

struct module_state {
  PyObject *ExtractorError;
};

#if PY_MAJOR_VERSION >= 3
#define GETSTATE(m) ((struct module_state*)PyModule_GetState(m))
#else
#define GETSTATE(m) (&_state)
static struct module_state _state;
#endif

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

static PyMethodDef kextractor_next_20200430_funcs[] = {
  {"kextract", (PyCFunction)kextract, METH_VARARGS, kextract_docs},
  {NULL}
};

#if PY_MAJOR_VERSION >= 3

static int kextractor_next_20200430_traverse(PyObject *m, visitproc visit, void *arg) {
    Py_VISIT(GETSTATE(m)->ExtractorError);
    return 0;
}

static int kextractor_next_20200430_clear(PyObject *m) {
    Py_CLEAR(GETSTATE(m)->ExtractorError);
    return 0;
}


static struct PyModuleDef kextractor_next_20200430def = {
        PyModuleDef_HEAD_INIT,
        "kextractor_next_20200430",
        NULL,
        sizeof(struct module_state),
        kextractor_next_20200430_funcs,
        NULL,
        kextractor_next_20200430_traverse,
        kextractor_next_20200430_clear,
        NULL
};

#define INITERROR return NULL

PyMODINIT_FUNC
PyInit_kextractor_next_20200430(void)

#else
#define INITERROR return

void initkextractor_next_20200430(void)
#endif
{
#if PY_MAJOR_VERSION >= 3
    PyObject *module = PyModule_Create(&kextractor_next_20200430def);
#else
    PyObject *module = Py_InitModule3("kextractor_next_20200430", kextractor_next_20200430_funcs,
                                      "Extract Kconfig dependencies.");
#endif

  if (module == NULL)
    INITERROR;
  struct module_state *st = GETSTATE(module);
  
  st->ExtractorError = PyErr_NewException("kextractor_next_20200430.error", NULL, NULL);
  if (st->ExtractorError == NULL) {
      Py_DECREF(module);
      INITERROR;
  }
  Py_INCREF(st->ExtractorError);
  PyModule_AddObject(module, "error", st->ExtractorError);

#if PY_MAJOR_VERSION >= 3
    return module;
#endif
}
