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

static PyMethodDef kextractor_4_12_8_funcs[] = {
  {"kextract", (PyCFunction)kextract, METH_VARARGS, kextract_docs},
  {NULL}
};

#if PY_MAJOR_VERSION >= 3

static int kextractor_4_12_8_traverse(PyObject *m, visitproc visit, void *arg) {
    Py_VISIT(GETSTATE(m)->ExtractorError);
    return 0;
}

static int kextractor_4_12_8_clear(PyObject *m) {
    Py_CLEAR(GETSTATE(m)->ExtractorError);
    return 0;
}


static struct PyModuleDef kextractor_4_12_8def = {
        PyModuleDef_HEAD_INIT,
        "kextractor_4_12_8",
        NULL,
        sizeof(struct module_state),
        kextractor_4_12_8_funcs,
        NULL,
        kextractor_4_12_8_traverse,
        kextractor_4_12_8_clear,
        NULL
};

#define INITERROR return NULL

PyMODINIT_FUNC
PyInit_kextractor_4_12_8(void)

#else
#define INITERROR return

void initkextractor_4_12_8(void)
#endif
{
#if PY_MAJOR_VERSION >= 3
    PyObject *module = PyModule_Create(&kextractor_4_12_8def);
#else
    PyObject *module = Py_InitModule3("kextractor_4_12_8", kextractor_4_12_8_funcs,
                                      "Extract Kconfig dependencies.");
#endif

  if (module == NULL)
    INITERROR;
  struct module_state *st = GETSTATE(module);
  
  st->ExtractorError = PyErr_NewException("kextractor_4_12_8.error", NULL, NULL);
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
