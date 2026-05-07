import Navigation from '../components/Navigation'
import { thoughtsLessonsContent } from '../data/content'

export default function MethodsPage() {
  return (
    <div
      className="min-h-screen"
      style={{ background: '#FAFAFA', paddingTop: '5rem', paddingBottom: '5rem' }}
    >
      <Navigation />

      <div style={{ maxWidth: 820, margin: '0 auto', padding: '0 2rem' }}>
        <h1
          className="font-inter font-bold text-center text-[#111111]"
          style={{ fontSize: '3rem', lineHeight: 1.1, margin: '0 0 3rem' }}
        >
          Thoughts &amp; Lessons
        </h1>

        <div
          style={{
            background: '#FFFFFF',
            border: '1px solid #111111',
            boxShadow: '3px 3px 0 rgba(0,0,0,0.08)',
            padding: '2rem 2.5rem',
          }}
        >
          {thoughtsLessonsContent.sections.map((section, i) => (
            <div
              key={i}
              style={{
                paddingBottom: i < thoughtsLessonsContent.sections.length - 1 ? '1.75rem' : 0,
                marginBottom: i < thoughtsLessonsContent.sections.length - 1 ? '1.75rem' : 0,
                borderBottom:
                  i < thoughtsLessonsContent.sections.length - 1
                    ? '1px solid #F0F0F0'
                    : 'none',
              }}
            >
              <h3
                className="font-inter font-bold text-[#444444]"
                style={{ fontSize: '1.25rem', margin: '0 0 0.75rem' }}
              >
                {section.title}
              </h3>
              <p
                className="font-inter text-[#444444]"
                style={{ fontSize: '0.9375rem', lineHeight: 1.7, margin: 0 }}
              >
                {section.body}
              </p>
            </div>
          ))}
        </div>
      </div>
    </div>
  )
}
