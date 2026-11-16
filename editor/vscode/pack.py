# The extension as a .vsix beside this file, for VS Code's
# `code --install-extension mara-<version>.vsix` (or Extensions view → … →
# Install from VSIX). A .vsix is a zip: its manifests, the extension's files
# under extension/. No npm or vsce needed.
import json, os, zipfile

here = os.path.dirname(os.path.abspath(__file__))
package = json.load(open(os.path.join(here, "package.json"), encoding="utf-8"))
files = ["package.json", "extension.js", "language-configuration.json", "syntaxes/mara.tmLanguage.json", "README.md"]
out = os.path.join(here, f"{package['name']}-{package['version']}.vsix")

content_types = """<?xml version="1.0" encoding="utf-8"?>
<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">
<Default Extension=".json" ContentType="application/json"/>
<Default Extension=".js" ContentType="application/javascript"/>
<Default Extension=".md" ContentType="text/markdown"/>
<Default Extension=".vsixmanifest" ContentType="text/xml"/>
</Types>
"""
manifest = f"""<?xml version="1.0" encoding="utf-8"?>
<PackageManifest Version="2.0.0" xmlns="http://schemas.microsoft.com/developer/vsx-schema/2011">
  <Metadata>
    <Identity Language="en-US" Id="{package['name']}" Version="{package['version']}" Publisher="{package['publisher']}"/>
    <DisplayName>{package['displayName']}</DisplayName>
    <Description xml:space="preserve">{package['description']}</Description>
    <Categories>{','.join(package['categories'])}</Categories>
    <Properties>
      <Property Id="Microsoft.VisualStudio.Code.Engine" Value="{package['engines']['vscode']}"/>
    </Properties>
  </Metadata>
  <Installation><InstallationTarget Id="Microsoft.VisualStudio.Code"/></Installation>
  <Dependencies/>
  <Assets>
    <Asset Type="Microsoft.VisualStudio.Code.Manifest" Path="extension/package.json" Addressable="true"/>
  </Assets>
</PackageManifest>
"""
with zipfile.ZipFile(out, "w", zipfile.ZIP_DEFLATED) as z:
    z.writestr("[Content_Types].xml", content_types)
    z.writestr("extension.vsixmanifest", manifest)
    for f in files:
        z.write(os.path.join(here, f), "extension/" + f)
print(out)
