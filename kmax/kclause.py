import re

def tristate_config_gen(option, value):
  """Create a Boolean config option to represent setting an option to tristate y or m.  == cannot appear in configuration option names, which avoids name clashes."""
  assert value == "y" or value == "m"
  return f"{option}=={value}"

tristate_pattern = re.compile("(CONFIG_[A-Za-z0-9_]+)==(y|m)")
