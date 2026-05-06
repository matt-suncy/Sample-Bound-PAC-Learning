import { useState } from 'react'
import Navigation from '../components/Navigation'
import MainTheoremBox from '../components/MainTheoremBox'
import DefinitionsBox from '../components/DefinitionsBox'
import CodePopup from '../components/CodePopup'
import type { TheoremNodeData } from '../data/graphData'

export default function Home() {
  const [codeNode, setCodeNode] = useState<TheoremNodeData | null>(null)

  return (
    <div
      className="min-h-screen"
      style={{ background: '#FAFAFA', paddingTop: '5rem', paddingBottom: '4rem' }}
    >
      <Navigation />

      <div style={{ maxWidth: 820, margin: '0 auto', padding: '0 2rem' }}>
        {/* Website title — Cormorant Garamond (swap class font-title to change) */}
        <h1
          className="font-title text-center text-[#111111]"
          style={{ fontSize: '4rem', fontWeight: 300, lineHeight: 1.2, margin: 0, letterSpacing: '0.01em' }}
        >
          AI Formalization of the Sample Complexity Bound of PAC Learning
        </h1>

        {/* Authors */}
        <p
          className="font-inter text-center text-[#444444]"
          style={{ fontSize: '0.9375rem', marginTop: '1.25rem', marginBottom: 0 }}
        >
          Erin Jaen and Matthew Sun
        </p>

        {/* Main Theorem Box */}
        <MainTheoremBox onOpenCode={setCodeNode} />

        {/* Definitions Box */}
        <DefinitionsBox />
      </div>

      {codeNode && (
        <CodePopup node={codeNode} onClose={() => setCodeNode(null)} />
      )}
    </div>
  )
}
